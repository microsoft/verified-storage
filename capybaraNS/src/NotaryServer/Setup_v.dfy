include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"
include "../Framework/PmemUtil_v.dfy"
include "Layout_v.dfy"
include "NotarySpec_t.dfy"

module NotarySetupModule {
import opened ExternalMethodsModule
import opened PersistentMemoryModule
import opened PmemUtilModule
import opened NativeTypesModule
import opened NotaryLayoutModule
import opened NotarySpecModule

lemma Lemma_SetupHelper(
    bytes: seq<byte>,
    keyPair: KeyView,
    keyPairBytes: seq<byte>,
    state: seq<byte>
)
    requires |bytes| == KEY_PAIR_POS as int
    requires |state| >= |bytes| + |keyPairBytes|
    requires state[0 .. KEY_PAIR_POS as int] == bytes[..]
    requires state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + |keyPairBytes|] == keyPairBytes
    requires bytes[CDB_POS as int .. CDB_POS as int + PERSISTENCE_CHUNK_SIZE] == SpecSerializeUint64(CDB_FALSE)
    requires bytes[COUNTER_POS0 as int .. COUNTER_POS0 as int + SIZEOF_UINT64] == SpecSerializeUint64(0)
    requires bytes[LAST_MESSAGE_POS0 as int .. LAST_MESSAGE_POS0 as int + NOTARIZED_MESSAGE_LENGTH] == SequenceOfZeroes(NOTARIZED_MESSAGE_LENGTH)
    requires bytes[DATA_CRC_POS0 as int .. DATA_CRC_POS0 as int + CRC_SIZE] == SpecCrcBytes(bytes[COUNTER_POS0 as int .. LAST_MESSAGE_POS0 as int + NOTARIZED_MESSAGE_LENGTH as int])
    requires ValidKeyView(keyPair)
    requires |keyPairBytes| <= 0x7FFF_FFFF
    requires bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64] == SpecSerializeUint64(|keyPairBytes| as uint64)
    requires bytes[KEY_PAIR_LENGTH_CRC_POS as int .. KEY_PAIR_LENGTH_CRC_POS as int + CRC_SIZE] == SpecCrcBytes(bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64])
    requires bytes[KEY_PAIR_CRC_POS as int .. KEY_PAIR_CRC_POS as int + CRC_SIZE] == SpecCrcBytes(keyPairBytes)
    requires SpecKeyViewSerializationCorrect(keyPair, keyPairBytes)
    ensures  RecoverNotaryState(state).Some?
    ensures  RecoverNotaryState(state).value.key == keyPair
    ensures  RecoverNotaryState(state).value.counter == 0
    ensures  RecoverNotaryState(state).value.lastMessage == SequenceOfZeroes(NOTARIZED_MESSAGE_LENGTH)
{
    var cdb := RecoverCDB(state);
    var keyPairLength := |keyPairBytes| as int32;
    assert ExtractBytes(state, CDB_POS as int, PERSISTENCE_CHUNK_SIZE) == bytes[CDB_POS as int .. CDB_POS as int + PERSISTENCE_CHUNK_SIZE];
    assert ExtractBytes(state, CDB_POS as int, PERSISTENCE_CHUNK_SIZE) == SpecSerializeUint64(CDB_FALSE);
    Axiom_SerializeDeserializeUint64(CDB_FALSE);
    assert cdb == Some(false);
    assert ExtractBytes(state, COUNTER_POS0 as int, SIZEOF_UINT64 as int) == bytes[COUNTER_POS0 as int .. COUNTER_POS0 as int + SIZEOF_UINT64 as int];
    assert ExtractBytes(state, COUNTER_POS0 as int, SIZEOF_UINT64 as int) == SpecSerializeUint64(0);
    Axiom_SerializeDeserializeUint64(0);
    assert ExtractBytes(state, DATA_CRC_POS0 as int, CRC_SIZE) == ExtractBytes(bytes, DATA_CRC_POS0 as int, CRC_SIZE);
    assert ExtractBytes(state, COUNTER_POS0 as int, SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH) ==
           ExtractBytes(bytes, COUNTER_POS0 as int, SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
    assert CheckDataCrc(false, state);
    assert RecoverCounter(false, state) == Some(0);
    assert ExtractBytes(state, LAST_MESSAGE_POS0 as int, NOTARIZED_MESSAGE_LENGTH) ==
            bytes[LAST_MESSAGE_POS0 as int .. LAST_MESSAGE_POS0 as int + NOTARIZED_MESSAGE_LENGTH];
    assert RecoverLastMessage(false, state) == SequenceOfZeroes(NOTARIZED_MESSAGE_LENGTH);
    assert ExtractBytes(state, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE) ==
            bytes[KEY_PAIR_LENGTH_CRC_POS as int .. KEY_PAIR_LENGTH_CRC_POS as int + CRC_SIZE as int];
    assert ExtractBytes(state, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64 as int) == SpecSerializeUint64(keyPairLength as uint64);
    Axiom_SerializeDeserializeUint64(keyPairLength as uint64);
    assert RecoverKeyPairLength(state) == Some(keyPairLength as uint64);
    assert ExtractBytes(state, KEY_PAIR_CRC_POS as int, CRC_SIZE) == bytes[KEY_PAIR_CRC_POS as int .. KEY_PAIR_CRC_POS as int + CRC_SIZE];
    assert ExtractBytes(state, KEY_PAIR_CRC_POS as int, CRC_SIZE) == SpecCrcBytes(keyPairBytes);
    assert ExtractBytes(state, KEY_PAIR_POS as int, keyPairLength as int) == keyPairBytes;
    Axiom_SerializeDeserializeKeyView(keyPair, keyPairBytes);
    assert RecoverKeyPair(state, keyPairLength as uint64) == Some(SpecDeserializeKeyView(keyPairBytes));
}

}
