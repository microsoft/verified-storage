include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"
include "../Framework/PmemUtil_v.dfy"
include "NotarySpec_t.dfy"

module NotaryLayoutModule {
import opened ExternalMethodsModule
import opened PersistentMemoryModule
import opened PmemUtilModule
import opened NativeTypesModule
import opened NotarySpecModule

const CDB_POS: int32 := 0
const DATA_CRC_POS0: int32 := 8
const COUNTER_POS0: int32 := 16
const LAST_MESSAGE_POS0: int32 := 24
const DATA_CRC_POS1: int32 := 56
const COUNTER_POS1: int32 := 64
const LAST_MESSAGE_POS1: int32 := 72
const KEY_PAIR_LENGTH_CRC_POS: int32 := 104
const KEY_PAIR_LENGTH_POS: int32 := 112
const KEY_PAIR_CRC_POS: int32 := 120
const KEY_PAIR_POS: int32 := 128
const NOTARIZED_MESSAGE_LENGTH_INT32: int32 := 32
const SIZEOF_UINT64_INT32: int32 := 8
const CRC_SIZE_INT32: int32 := 8

ghost function RecoverCDB(state: seq<byte>) : Option<bool>
    requires |state| >= KEY_PAIR_POS as int
{
    var cdbBytes := ExtractBytes(state, CDB_POS as int, PERSISTENCE_CHUNK_SIZE);
    var cdbVal := SpecDeserializeUint64(cdbBytes);
    if cdbVal == CDB_TRUE then
        Some(true)
    else if cdbVal == CDB_FALSE then
        Some(false)
    else
        None
}

ghost predicate CheckDataCrc(cdb: bool, state: seq<byte>)
    requires |state| >= KEY_PAIR_POS as int
{
    var dataPos := if cdb then COUNTER_POS1 else COUNTER_POS0;
    var crcPos := if cdb then DATA_CRC_POS1 else DATA_CRC_POS0;
    var dataBytes := ExtractBytes(state, dataPos as int, SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
    var crcBytes := ExtractBytes(state, crcPos as int, CRC_SIZE);
    crcBytes == SpecCrcBytes(dataBytes)
}

ghost function RecoverCounter(cdb: bool, state: seq<byte>) : Option<uint64>
    requires |state| >= KEY_PAIR_POS as int
{
    var counterPos := if cdb then COUNTER_POS1 else COUNTER_POS0;
    var bytes := ExtractBytes(state, counterPos as int, SIZEOF_UINT64);
    var counter := SpecDeserializeUint64(bytes);
    if bytes == SpecSerializeUint64(counter) then
        Some(counter)
    else
        None
}

ghost function RecoverLastMessage(cdb: bool, state: seq<byte>) : seq<byte>
    requires |state| >= KEY_PAIR_POS as int
{
    if cdb then
        ExtractBytes(state, LAST_MESSAGE_POS1 as int, NOTARIZED_MESSAGE_LENGTH)
    else
        ExtractBytes(state, LAST_MESSAGE_POS0 as int, NOTARIZED_MESSAGE_LENGTH)
}

ghost function RecoverKeyPairLength(state: seq<byte>) : Option<uint64>
    requires |state| >= KEY_PAIR_POS as int
{
    var crcBytes := ExtractBytes(state, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE);
    var keyPairLengthBytes := ExtractBytes(state, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64);
    if SpecCrcBytes(keyPairLengthBytes) == crcBytes then
        Some(SpecDeserializeUint64(keyPairLengthBytes))
    else
        None
}

ghost function RecoverKeyPair(state: seq<byte>, keyPairLength: uint64) : Option<KeyView>
    requires |state| >= KEY_PAIR_POS as int + keyPairLength as int
{
    var crcBytes := ExtractBytes(state, KEY_PAIR_CRC_POS as int, CRC_SIZE);
    var keyPairBytes := ExtractBytes(state, KEY_PAIR_POS as int, keyPairLength as int);
    var keyView := SpecDeserializeKeyView(keyPairBytes);
    if ValidKeyView(keyView) && SpecCrcBytes(keyPairBytes) == crcBytes then
        Some(keyView)
    else
        None
}

ghost function RecoverNotaryState(state: seq<byte>) : Option<NotaryServerState>
{
    if |state| < KEY_PAIR_POS as int then
        None
    else
        var cdb := RecoverCDB(state);
        if cdb.None? then
            None
        else if !CheckDataCrc(cdb.value, state) then
            None
        else
            var counter := RecoverCounter(cdb.value, state);
            var lastMessage := RecoverLastMessage(cdb.value, state);
            var keyPairLength := RecoverKeyPairLength(state);
            if || counter.None?
               || keyPairLength.None?
               || keyPairLength.value > 0x7FFF_FFFF
               || |state| < KEY_PAIR_POS as int + keyPairLength.value as int then
                None
            else
                var keyPair := RecoverKeyPair(state, keyPairLength.value);
                if keyPair.None? then
                    None
                else
                    Some(NotaryServerState(keyPair.value, counter.value, lastMessage))
}

}
