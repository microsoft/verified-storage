include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"
include "../Framework/PmemUtil_v.dfy"
include "Layout_v.dfy"
include "NotarySpec_t.dfy"
include "Util_v.dfy"

module NotaryStartModule {
import opened ExternalMethodsModule
import opened PersistentMemoryModule
import opened PmemUtilModule
import opened NativeTypesModule
import opened NotaryLayoutModule
import opened NotarySpecModule
import opened NotaryUtilModule

lemma Lemma_StartHelper1(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    cdbValue: uint64
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires cdbValue == SpecDeserializeUint64(bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64])
    requires cdbValue != CDB_TRUE && cdbValue != CDB_FALSE
    ensures  !imperviousToCorruption
{
    assert imperviousToCorruption ==>
           state[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64] == bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64];
    if cdbValue != CDB_FALSE && cdbValue != CDB_TRUE {
        assert state[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64] != bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64];
        assert !imperviousToCorruption;
    }
}

lemma Lemma_StartHelper2(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    cdbValue: uint64,
    cdb: bool
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires cdbValue == SpecDeserializeUint64(bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64])
    requires cdbValue == CDB_TRUE || cdbValue == CDB_FALSE
    requires cdb == (cdbValue == CDB_TRUE)
    ensures  cdb == RecoverCDB(state).value
{
    assert imperviousToCorruption ==>
           state[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64] == bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64];
    assert cdb == RecoverCDB(state).value by {
        if !imperviousToCorruption {
            Axiom_CorruptionDetectingBoolean(bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64],
                                             state[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64],
                                             seq(SIZEOF_UINT64, i => i as int + CDB_POS as int));
        }
    }
}

lemma Lemma_StartHelper3(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    cdb: bool,
    dataPos: int,
    crcPos: int,
    crcBuffer: seq<byte>
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires cdb == RecoverCDB(state).value
    requires dataPos == (if cdb then COUNTER_POS1 else COUNTER_POS0) as int
    requires crcPos == (if cdb then DATA_CRC_POS1 else DATA_CRC_POS0) as int
    requires crcBuffer == SpecCrcBytes(bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH])
    requires crcBuffer[0 .. CRC_SIZE] != bytes[crcPos .. crcPos + CRC_SIZE]
    ensures  !imperviousToCorruption
{
    Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
    Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
    Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, crcPos, crcPos + CRC_SIZE);
    Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, crcPos, crcPos + CRC_SIZE);
}

lemma Lemma_StartHelper4(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    cdb: bool,
    dataPos: int,
    crcPos: int,
    messagePos: int,
    crcBuffer: seq<byte>
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires cdb == RecoverCDB(state).value
    requires dataPos == (if cdb then COUNTER_POS1 else COUNTER_POS0) as int
    requires crcPos == (if cdb then DATA_CRC_POS1 else DATA_CRC_POS0) as int
    requires messagePos == (if cdb then LAST_MESSAGE_POS1 else LAST_MESSAGE_POS0) as int
    requires crcBuffer == SpecCrcBytes(bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH])
    requires crcBuffer[0 .. CRC_SIZE] == bytes[crcPos .. crcPos + CRC_SIZE]
    ensures  bytes[dataPos .. dataPos + SIZEOF_UINT64] == state[dataPos .. dataPos + SIZEOF_UINT64]
    ensures  bytes[messagePos .. messagePos + NOTARIZED_MESSAGE_LENGTH] == state[messagePos .. messagePos + NOTARIZED_MESSAGE_LENGTH]
{
    assert bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] ==
           state[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] by {
        if !imperviousToCorruption {
            forall i: int {:trigger bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH][i]}
                | 0 <= i < SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH
                ensures MaybeCorruptedByte(bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH][i],
                                           state[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH][i],
                                           seq(SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH, i => i as int + dataPos)[i])
            {
                assert bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH][i] == bytes[dataPos + i];
                assert state[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH][i] ==
                       state[0 .. KEY_PAIR_POS][dataPos + i];
                assert MaybeCorruptedByte(bytes[dataPos + i], state[0 .. KEY_PAIR_POS][dataPos + i], dataPos + i);
            }
            Axiom_BytesUncorrupted(bytes[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH],
                                   state[dataPos .. dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH],
                                   seq(SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH, i => i as int + dataPos as int),
                                   bytes[crcPos .. crcPos + CRC_SIZE],
                                   state[crcPos .. crcPos + CRC_SIZE],
                                   seq(CRC_SIZE, i => i as int + crcPos));
        }
        Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
        Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
    }

    Lemma_SubrangeOfSubrange(state, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH, dataPos, dataPos + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(bytes, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH, dataPos, dataPos + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(state, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH, messagePos, messagePos + NOTARIZED_MESSAGE_LENGTH);
    Lemma_SubrangeOfSubrange(bytes, dataPos, dataPos + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH, messagePos, messagePos + NOTARIZED_MESSAGE_LENGTH);
}

lemma Lemma_StartHelper5(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    crcBuffer: seq<byte>
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires crcBuffer == SpecCrcBytes(bytes[KEY_PAIR_LENGTH_POS .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64])
    requires crcBuffer[0 .. CRC_SIZE] != bytes[KEY_PAIR_LENGTH_CRC_POS .. KEY_PAIR_LENGTH_CRC_POS as int + CRC_SIZE]
    ensures  !imperviousToCorruption
{
    Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, KEY_PAIR_LENGTH_POS as int, KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, KEY_PAIR_LENGTH_POS as int, KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, KEY_PAIR_LENGTH_CRC_POS as int, KEY_PAIR_LENGTH_CRC_POS as int + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, KEY_PAIR_LENGTH_CRC_POS as int, KEY_PAIR_LENGTH_CRC_POS as int + SIZEOF_UINT64);
}

lemma Lemma_StartHelper6(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    crcBuffer: seq<byte>
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires crcBuffer == SpecCrcBytes(bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64])
    requires crcBuffer[0 .. CRC_SIZE] == bytes[KEY_PAIR_LENGTH_CRC_POS as int .. KEY_PAIR_LENGTH_CRC_POS as int + CRC_SIZE]
    ensures  bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64] == state[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64]
{
    if !imperviousToCorruption {
        forall i: int {:trigger bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64][i]}
            | 0 <= i < SIZEOF_UINT64
            ensures MaybeCorruptedByte(bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64][i],
                                        state[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64][i],
                                        seq(SIZEOF_UINT64, i => i as int + KEY_PAIR_LENGTH_POS as int)[i])
        {
            assert bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64][i] == bytes[KEY_PAIR_LENGTH_POS as int + i];
            assert state[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64][i] == state[KEY_PAIR_LENGTH_POS as int + i];
            assert MaybeCorruptedByte(bytes[KEY_PAIR_LENGTH_POS as int + i], state[KEY_PAIR_LENGTH_POS as int + i], KEY_PAIR_LENGTH_POS as int + i);
        }
        Axiom_BytesUncorrupted(bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64],
                                state[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64],
                                seq(SIZEOF_UINT64, i => i as int + KEY_PAIR_LENGTH_POS as int),
                                bytes[KEY_PAIR_LENGTH_CRC_POS as int .. KEY_PAIR_LENGTH_CRC_POS as int + CRC_SIZE],
                                state[KEY_PAIR_LENGTH_CRC_POS as int .. KEY_PAIR_LENGTH_CRC_POS as int + CRC_SIZE],
                                seq(CRC_SIZE, i => i as int + KEY_PAIR_LENGTH_CRC_POS as int));
    }
    Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, KEY_PAIR_LENGTH_POS as int, KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, KEY_PAIR_LENGTH_POS as int, KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64);
}

lemma Lemma_StartHelper7(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    keyPairLength: uint64,
    keyPairBytes: seq<byte>,
    crcBuffer: seq<byte>
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int + keyPairLength as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires keyPairLength == RecoverKeyPairLength(state).value
    requires imperviousToCorruption ==> keyPairBytes == state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int]
    requires !imperviousToCorruption ==> MaybeCorrupted(keyPairBytes, state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int],
                                                        seq(keyPairLength as nat, i => i as int + KEY_PAIR_POS as int))
    requires crcBuffer == SpecCrcBytes(keyPairBytes)
    requires crcBuffer[0 .. CRC_SIZE] != bytes[KEY_PAIR_CRC_POS as int .. KEY_PAIR_CRC_POS as int + CRC_SIZE]
    ensures  !imperviousToCorruption
{
    Lemma_SubrangeOfSubrange(bytes, 0, KEY_PAIR_POS as int, KEY_PAIR_CRC_POS as int, KEY_PAIR_CRC_POS as int + SIZEOF_UINT64);
    Lemma_SubrangeOfSubrange(state, 0, KEY_PAIR_POS as int, KEY_PAIR_CRC_POS as int, KEY_PAIR_CRC_POS as int + SIZEOF_UINT64);
}

lemma Lemma_StartHelper8(
    state: seq<byte>,
    bytes: seq<byte>,
    imperviousToCorruption: bool,
    keyPairLength: uint64,
    keyPairBytes: seq<byte>,
    crcBuffer: seq<byte>
)
    requires RecoverNotaryState(state).Some?
    requires |state| >= KEY_PAIR_POS as int + keyPairLength as int
    requires imperviousToCorruption ==> bytes == state[0 .. KEY_PAIR_POS]
    requires !imperviousToCorruption ==> MaybeCorrupted(bytes, state[0 .. KEY_PAIR_POS], seq(KEY_PAIR_POS, i => i as int))
    requires keyPairLength == RecoverKeyPairLength(state).value
    requires imperviousToCorruption ==> keyPairBytes == state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int]
    requires !imperviousToCorruption ==> MaybeCorrupted(keyPairBytes, state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int],
                                                        seq(keyPairLength as nat, i => i as int + KEY_PAIR_POS as int))
    requires crcBuffer == SpecCrcBytes(keyPairBytes)
    requires crcBuffer[0 .. CRC_SIZE] == bytes[KEY_PAIR_CRC_POS as int .. KEY_PAIR_CRC_POS as int + CRC_SIZE]
    ensures  keyPairBytes[0 .. keyPairLength as int] == state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int]
{
    if !imperviousToCorruption {
        Axiom_BytesUncorrupted(keyPairBytes,
                               state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int],
                               seq(keyPairLength as int, i => i as int + KEY_PAIR_POS as int),
                               bytes[KEY_PAIR_CRC_POS as int .. KEY_PAIR_CRC_POS as int + CRC_SIZE],
                               state[KEY_PAIR_CRC_POS as int .. KEY_PAIR_CRC_POS as int + CRC_SIZE],
                               seq(CRC_SIZE, i => i as int + KEY_PAIR_CRC_POS as int));
    }
    assert(keyPairBytes == keyPairBytes[0 .. keyPairLength as int]);
}

}
