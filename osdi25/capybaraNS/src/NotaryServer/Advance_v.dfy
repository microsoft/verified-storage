include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"
include "../Framework/PmemUtil_v.dfy"
include "Layout_v.dfy"
include "NotarySpec_t.dfy"
include "Util_v.dfy"

module NotaryAdvanceModule {
import opened ExternalMethodsModule
import opened PersistentMemoryModule
import opened PmemUtilModule
import opened NativeTypesModule
import opened NotaryLayoutModule
import opened NotarySpecModule
import opened NotaryUtilModule

lemma Lemma_UnreachableAddressDoesntAffectRecovery(
    state1: seq<byte>,
    state2: seq<byte>,
    cdb: bool,
    addr: int
)
    requires RecoverNotaryState(state1).Some?
    requires cdb == RecoverCDB(state1).value
    requires var unreachablePos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
             unreachablePos <= addr < unreachablePos + CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH
    requires |state2| == |state1|
    requires forall i: int :: 0 <= i < |state1| && i != addr ==>
             state1[i] == state2[i]
    ensures  RecoverNotaryState(state2) == RecoverNotaryState(state1)
    ensures  cdb == RecoverCDB(state2).value
{
    var crcPos := (if cdb then DATA_CRC_POS1 else DATA_CRC_POS0) as int;
    var counterPos := (if cdb then COUNTER_POS1 else COUNTER_POS0) as int;
    var messagePos := (if cdb then LAST_MESSAGE_POS1 else LAST_MESSAGE_POS0) as int;
    var unreachablePos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
    assert ExtractBytes(state1, CDB_POS as int, PERSISTENCE_CHUNK_SIZE) ==
           ExtractBytes(state2, CDB_POS as int, PERSISTENCE_CHUNK_SIZE);
    assert cdb == RecoverCDB(state2).value;
    assert ExtractBytes(state1, counterPos, SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH) ==
           ExtractBytes(state2, counterPos, SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
    assert ExtractBytes(state1, crcPos, CRC_SIZE) == ExtractBytes(state2, crcPos, CRC_SIZE);
    assert CheckDataCrc(cdb, state2);
    assert ExtractBytes(state1, counterPos, SIZEOF_UINT64) ==
           ExtractBytes(state2, counterPos, SIZEOF_UINT64);
    assert ExtractBytes(state1, counterPos, SIZEOF_UINT64) == ExtractBytes(state2, counterPos, SIZEOF_UINT64);
    assert RecoverCounter(cdb, state2) == RecoverCounter(cdb, state1);
    assert ExtractBytes(state1, messagePos, NOTARIZED_MESSAGE_LENGTH) ==
           ExtractBytes(state2, messagePos, NOTARIZED_MESSAGE_LENGTH) by {
        forall i: int | 0 <= i < NOTARIZED_MESSAGE_LENGTH
            ensures
                ExtractBytes(state1, messagePos, NOTARIZED_MESSAGE_LENGTH)[i] ==
                ExtractBytes(state2, messagePos, NOTARIZED_MESSAGE_LENGTH)[i]
        {
            calc {
                ExtractBytes(state1, messagePos, NOTARIZED_MESSAGE_LENGTH)[i];
                state1[messagePos .. messagePos + NOTARIZED_MESSAGE_LENGTH][i];
                state1[messagePos + i];
            }
            assert |state2| >= messagePos + NOTARIZED_MESSAGE_LENGTH;
            calc {
                ExtractBytes(state2, messagePos, NOTARIZED_MESSAGE_LENGTH)[i];
                state2[messagePos .. messagePos + NOTARIZED_MESSAGE_LENGTH][i];
                state2[messagePos + i];
            }
            assert !(unreachablePos <= messagePos + i < unreachablePos + CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH);
        }
    }
    assert RecoverLastMessage(cdb, state2) == RecoverLastMessage(cdb, state1);
    assert ExtractBytes(state1, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE) ==
           ExtractBytes(state2, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE);
    assert ExtractBytes(state1, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64) ==
           ExtractBytes(state2, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64);
    assert RecoverKeyPairLength(state2) == RecoverKeyPairLength(state1);
    var keyPairLength := RecoverKeyPairLength(state1).value;
    assert ExtractBytes(state1, KEY_PAIR_CRC_POS as int, CRC_SIZE) ==
           ExtractBytes(state2, KEY_PAIR_CRC_POS as int, CRC_SIZE);
    assert ExtractBytes(state1, KEY_PAIR_POS as int, keyPairLength as int) ==
           ExtractBytes(state2, KEY_PAIR_POS as int, keyPairLength as int);
    assert RecoverKeyPair(state2, keyPairLength) == RecoverKeyPair(state1, keyPairLength);
    assert RecoverNotaryState(state2) == RecoverNotaryState(state1);
}

lemma lemma_UnreachabilityCondition(
    state: seq<byte>,
    cdb: bool
)
    requires RecoverNotaryState(state).Some?
    requires cdb == RecoverCDB(state).value
    ensures  var unreachablePos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
             var condition := (iset s | RecoverNotaryState(s).Some? && cdb == RecoverCDB(s).value && RecoverNotaryState(s) == RecoverNotaryState(state));
             forall addr: int :: unreachablePos <= addr < unreachablePos + CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH ==>
             AddressDoesntAffectCondition(addr, condition)
{
    var unreachablePos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
    var condition := (iset s | (
        && RecoverNotaryState(s).Some?
        && cdb == RecoverCDB(s).value
        && RecoverNotaryState(s) == RecoverNotaryState(state)
    ));
    forall addr: int | unreachablePos <= addr < unreachablePos + CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH
        ensures AddressDoesntAffectCondition(addr, condition)
    {
        forall s: seq<byte>, s': seq<byte> | (
            && s in condition
            && |s'| == |s|
            && (forall i: int :: 0 <= i < |s| && i != addr ==> s[i] == s'[i])
        ) ensures s' in condition {
            Lemma_UnreachableAddressDoesntAffectRecovery(s, s', cdb, addr);
        }
    }
}

lemma lemma_AdvanceHelper1(
    wrpm: PersistentMemoryRegion,
    cdb: bool,
    bytes: seq<byte>,
    start: int
)
    requires wrpm.Valid()
    requires RecoverNotaryState(wrpm.View().durableState).Some?
    requires cdb == RecoverCDB(wrpm.View().durableState).value
    requires forall s: seq<byte> {:trigger s in wrpm.StatesPermitted()} ::
                 RecoverNotaryState(s) == RecoverNotaryState(wrpm.View().durableState) ==>
                 s in wrpm.StatesPermitted()
    requires var unreachablePos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
             && unreachablePos <= start
             && start + |bytes| <= unreachablePos + CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH
    ensures  forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } ::
                CanResultFromPartialWrite(s, wrpm.View().durableState, start, bytes)
                ==> s in wrpm.StatesPermitted()
{
    var unreachablePos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
    forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() }
        | CanResultFromPartialWrite(s, wrpm.View().durableState, start, bytes)
        ensures s in wrpm.StatesPermitted()
    {
        lemma_UnreachabilityCondition(wrpm.View().durableState, cdb);
        var condition := (iset s | (
            && RecoverNotaryState(s).Some?
            && cdb == RecoverCDB(s).value
            && RecoverNotaryState(s) == RecoverNotaryState(wrpm.View().durableState)
        ));
        Lemma_IfAddressesDontAffectConditionThenWritePermitted(wrpm, condition, bytes, start);
    }
}

lemma lemma_AdvanceHelper2(
    wrpm: PersistentMemoryRegion,
    prevBytes: seq<byte>,
    currentBytes: seq<byte>,
    cdb: bool,
    newCounter: uint64,
    newMessage: seq<byte>,
    bytes: seq<byte>
)
    requires wrpm.Valid()
    requires wrpm.View().durableState == wrpm.View().readState == currentBytes
    requires
        var state := RecoverNotaryState(prevBytes);
        && state.Some?
        && (forall s: seq<byte> :: RecoverNotaryState(s) == state ==> s in wrpm.StatesPermitted())
        && (forall s: seq<byte> ::
                RecoverNotaryState(s).Some? && AdvanceCorrect(state.value, RecoverNotaryState(s).value, newMessage[..], true, true) ==>
                s in wrpm.StatesPermitted())
    requires newCounter > 0
    requires RecoverNotaryState(prevBytes).Some?
    requires RecoverNotaryState(prevBytes).value.counter == newCounter - 1
    requires |bytes| == CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH
    requires bytes[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64] == SpecSerializeUint64(newCounter)
    requires bytes[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] == newMessage
    requires bytes[0 .. CRC_SIZE] == SpecCrcBytes(bytes[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH])
    requires var unusedCrcPos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
             currentBytes == UpdateBytes(prevBytes, unusedCrcPos, bytes)
    ensures  var newCdbValue := if cdb then CDB_FALSE else CDB_TRUE;
             var newCdbBytes := SpecSerializeUint64(newCdbValue);
             var newBytes := UpdateBytes(currentBytes, CDB_POS as int, newCdbBytes);
             var state := RecoverNotaryState(prevBytes);
             var state' := RecoverNotaryState(newBytes);
             && state.Some?
             && state'.Some?
             && state'.value.counter == newCounter
             && state'.value.lastMessage == newMessage
             && state'.value.key == state.value.key
             && AdvanceCorrect(state.value, state'.value, newMessage, wrpm.constants.imperviousToCorruption, true)
             && RecoverCDB(newBytes) == Some(!cdb)
{
    var unusedCrcPos := (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int;
    var newCdbValue := if cdb then CDB_FALSE else CDB_TRUE;
    var newCdbBytes := SpecSerializeUint64(newCdbValue);
    var newBytes := UpdateBytes(currentBytes, CDB_POS as int, newCdbBytes);
    assert ExtractBytes(newBytes, CDB_POS as int, PERSISTENCE_CHUNK_SIZE) == newCdbBytes;
    Axiom_SerializeDeserializeUint64(newCdbValue);
    assert RecoverCDB(newBytes) == Some(!cdb);
    var dataPos: int32 := if !cdb then COUNTER_POS1 else COUNTER_POS0;
    var crcPos: int32 := if !cdb then DATA_CRC_POS1 else DATA_CRC_POS0;
    var messagePos: int32 := if !cdb then LAST_MESSAGE_POS1 else LAST_MESSAGE_POS0;
    assert ExtractBytes(newBytes, dataPos as int, SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH) ==
           bytes[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH];
    assert CheckDataCrc(!cdb, newBytes);
    assert ExtractBytes(newBytes, dataPos as int, SIZEOF_UINT64) ==
           ExtractBytes(currentBytes, dataPos as int, SIZEOF_UINT64);
    assert ExtractBytes(newBytes, dataPos as int, SIZEOF_UINT64) == bytes[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64];
    Axiom_SerializeDeserializeUint64(newCounter);
    assert RecoverCounter(!cdb, newBytes) == Some(newCounter);

    assert ExtractBytes(newBytes, messagePos as int, NOTARIZED_MESSAGE_LENGTH) ==
           ExtractBytes(currentBytes, messagePos as int, NOTARIZED_MESSAGE_LENGTH) by {
        Lemma_SubrangeOfSubrange(newBytes, 0, |newBytes|, messagePos as int,
                                 messagePos as int + NOTARIZED_MESSAGE_LENGTH);
        Lemma_SubrangeOfSubrange(currentBytes, 0, |currentBytes|, messagePos as int,
                                 messagePos as int + NOTARIZED_MESSAGE_LENGTH);
    }
    assert ExtractBytes(newBytes, messagePos as int, NOTARIZED_MESSAGE_LENGTH) ==
           bytes[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH];
    assert ExtractBytes(newBytes, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE) ==
           ExtractBytes(currentBytes, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE) ==
           ExtractBytes(prevBytes, KEY_PAIR_LENGTH_CRC_POS as int, CRC_SIZE);
    assert ExtractBytes(newBytes, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64) ==
           ExtractBytes(currentBytes, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64) ==
           ExtractBytes(prevBytes, KEY_PAIR_LENGTH_POS as int, SIZEOF_UINT64);
    assert RecoverKeyPairLength(newBytes) == RecoverKeyPairLength(currentBytes) == RecoverKeyPairLength(prevBytes);
    var keyPairLength := RecoverKeyPairLength(prevBytes).value;
    assert ExtractBytes(newBytes, KEY_PAIR_CRC_POS as int, CRC_SIZE) ==
           ExtractBytes(currentBytes, KEY_PAIR_CRC_POS as int, CRC_SIZE) ==
           ExtractBytes(prevBytes, KEY_PAIR_CRC_POS as int, CRC_SIZE);
    assert ExtractBytes(newBytes, KEY_PAIR_POS as int, keyPairLength as int) ==
           ExtractBytes(currentBytes, KEY_PAIR_POS as int, keyPairLength as int) ==
           ExtractBytes(prevBytes, KEY_PAIR_POS as int, keyPairLength as int) by {
        forall i: int {:trigger ExtractBytes(currentBytes, KEY_PAIR_POS as int, keyPairLength as int)[i]}
            | 0 <= i < keyPairLength as int
            ensures
                ExtractBytes(currentBytes, KEY_PAIR_POS as int, keyPairLength as int)[i] ==
                ExtractBytes(prevBytes, KEY_PAIR_POS as int, keyPairLength as int)[i]
        {
            assert ExtractBytes(currentBytes, KEY_PAIR_POS as int, keyPairLength as int)[i] ==
                   currentBytes[KEY_PAIR_POS as int + i];
            assert ExtractBytes(prevBytes, KEY_PAIR_POS as int, keyPairLength as int)[i] ==
                   prevBytes[KEY_PAIR_POS as int + i];
            assert currentBytes[KEY_PAIR_POS as int + i] == prevBytes[KEY_PAIR_POS as int + i];
        }
    }
    assert RecoverKeyPair(newBytes, keyPairLength) ==
           RecoverKeyPair(currentBytes, keyPairLength) == RecoverKeyPair(prevBytes, keyPairLength);
}

}
