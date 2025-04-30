include "NativeTypes_t.dfy"
include "PersistentMemory_t.dfy"

module PmemUtilModule {
import opened NativeTypesModule
import opened PersistentMemoryModule

ghost function ExtractBytes(s: seq<byte>, start: int, length: int) : seq<byte>
    requires 0 <= start
    requires 0 <= length
    requires start + length <= |s|
{
    s[start .. start + length]
}

ghost predicate AddressesNotAccessedByRecovery<T>(s: seq<byte>, addrs: set<int>, recover_fn: seq<byte> -> T)
{
    forall s': seq<byte> :: (
        && |s'| == |s|
        && (forall i: int :: 0 <= i < |s| && i !in addrs ==> s[i] == s'[i])
    ) ==> recover_fn(s') == recover_fn(s)
}

lemma Lemma_IfAddressesNotAccessedByRecoveryThenWritePermitted<T>(
    wrpm: PersistentMemoryRegion,
    addrs: set<int>,
    recover_fn: seq<byte> -> T,
    bytes: seq<byte>,
    start: int
)
    requires wrpm.Valid()
    requires forall s: seq<byte> :: recover_fn(s) == recover_fn(wrpm.View().durableState) ==>
             s in wrpm.StatesPermitted()
    requires AddressesNotAccessedByRecovery(wrpm.View().durableState, addrs, recover_fn)
    requires forall addr: int :: start <= addr < start + |bytes| ==> addr in addrs
    ensures  forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } ::
                CanResultFromPartialWrite(s, wrpm.View().durableState, start, bytes)
                ==> s in wrpm.StatesPermitted()
{
    forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } |
        CanResultFromPartialWrite(s, wrpm.View().durableState, start as int, bytes)
        ensures s in wrpm.StatesPermitted()
    {
        forall addr: int | 0 <= addr < start || start + |bytes| <= addr < |wrpm.View().durableState|
            ensures s[addr] == wrpm.View().durableState[addr]
        {               
            assert(ChunkTrigger(addr / PERSISTENCE_CHUNK_SIZE));
        }
    }
}

ghost predicate AddressDoesntAffectCondition(addr: int, condition: iset<seq<byte>>)
{
    forall s: seq<byte>, s': seq<byte> :: (
        && s in condition
        && |s'| == |s|
        && (forall i: int :: 0 <= i < |s| && i != addr ==> s[i] == s'[i])
    ) ==> s' in condition
}

lemma Lemma_IfAddressesDontAffectConditionThenConditionPreserved(
    condition: iset<seq<byte>>,
    s: seq<byte>,
    s': seq<byte>,
    start: int,
    length: int
)
    requires |s| == |s'|
    requires 0 <= start
    requires 0 <= length
    requires start + length <= |s|
    requires forall addr: int :: 0 <= addr < start || start + length <= addr < |s| ==> s'[addr] == s[addr]
    requires forall addr: int :: start <= addr < start + length ==> AddressDoesntAffectCondition(addr, condition)
    requires s in condition
    ensures  s' in condition
    decreases length
{
    if length == 0 {
        assert s' == s;
    }
    else {
        var s_mid := s[start := s'[start]];
        assert(AddressDoesntAffectCondition(start, condition));
        assert(s_mid in condition);
        Lemma_IfAddressesDontAffectConditionThenConditionPreserved(condition, s_mid, s', start + 1, length - 1);
    }
}

lemma Lemma_IfAddressesDontAffectConditionThenWritePermitted(
    wrpm: PersistentMemoryRegion,
    condition: iset<seq<byte>>,
    bytes: seq<byte>,
    start: int
)
    requires wrpm.Valid()
    requires wrpm.View().durableState in condition
    requires forall s: seq<byte> :: s in condition ==> s in wrpm.StatesPermitted()
    requires forall addr: int :: start <= addr < start + |bytes| ==> AddressDoesntAffectCondition(addr, condition)
    ensures  forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } ::
                CanResultFromPartialWrite(s, wrpm.View().durableState, start, bytes)
                ==> s in wrpm.StatesPermitted()
{
    forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } |
        CanResultFromPartialWrite(s, wrpm.View().durableState, start as int, bytes)
        ensures s in wrpm.StatesPermitted()
    {
        forall addr: int | 0 <= addr < start || start + |bytes| <= addr < |wrpm.View().durableState|
            ensures s[addr] == wrpm.View().durableState[addr]
        {               
            assert(ChunkTrigger(addr / PERSISTENCE_CHUNK_SIZE));
        }
        Lemma_IfAddressesDontAffectConditionThenConditionPreserved(condition, wrpm.View().durableState, s, start, |bytes|);
    }
}

lemma Lemma_OnlyTwoPossibleCrashStatesWhenWritingAlignedChunk(
    s: seq<byte>,
    s': seq<byte>,
    start: int,
    bytes: seq<byte>
)
    requires |bytes| == PERSISTENCE_CHUNK_SIZE
    requires start % PERSISTENCE_CHUNK_SIZE == 0
    requires CanResultFromPartialWrite(s', s, start, bytes)
    ensures  s' == s || s' == UpdateBytes(s, start, bytes)
{
    var chunk := start / PERSISTENCE_CHUNK_SIZE;
    assert(ChunkTrigger(chunk));
    var s'' := if ChunkCorresponds(s', s, chunk) then s else UpdateBytes(s, start, bytes);
    forall i: int | 0 <= i < |s|
        ensures s'[i] == s''[i]
    {
        if i / PERSISTENCE_CHUNK_SIZE != chunk {
            assert 0 <= i < start || start + |bytes| <= i < |s|;
            assert(ChunkTrigger(i / PERSISTENCE_CHUNK_SIZE));
        }
    }
    assert(s' == s'');
}

lemma Lemma_WritingAlignedChunkPermittedIfFullWritePermitted(
    wrpm: PersistentMemoryRegion,
    start: int,
    bytes: seq<byte>
)
    requires wrpm.Valid()
    requires wrpm.View().durableState in wrpm.StatesPermitted()
    requires 0 <= start
    requires start + |bytes| <= |wrpm.View().durableState|
    requires start % PERSISTENCE_CHUNK_SIZE == 0
    requires |bytes| == PERSISTENCE_CHUNK_SIZE
    requires UpdateBytes(wrpm.View().durableState, start, bytes) in wrpm.StatesPermitted()
    ensures  forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } ::
                CanResultFromPartialWrite(s, wrpm.View().durableState, start, bytes)
                ==> s in wrpm.StatesPermitted()
{
    forall s: seq<byte> {:trigger s in wrpm.StatesPermitted() } |
        CanResultFromPartialWrite(s, wrpm.View().durableState, start, bytes)
        ensures s in wrpm.StatesPermitted()
    {
        Lemma_OnlyTwoPossibleCrashStatesWhenWritingAlignedChunk(wrpm.View().durableState, s, start, bytes);
    }
}

}
