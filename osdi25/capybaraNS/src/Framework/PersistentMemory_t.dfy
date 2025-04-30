include "NativeTypes_t.dfy"

module PersistentMemoryModule {

import opened NativeTypesModule

ghost predicate MaybeCorruptedByte(read_value: byte, true_value: byte, addr: int)

ghost predicate AllElementsUnique(s: seq<int>)
{
    forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] != s[j]
}

ghost predicate MaybeCorrupted(readValues: seq<byte>, trueValues: seq<byte>, addrs: seq<int>)
{
    && |readValues| == |trueValues| == |addrs|
    && forall i: int {:trigger readValues[i]} :: 0 <= i < |readValues| ==> MaybeCorruptedByte(readValues[i], trueValues[i], addrs[i])
}

const CRC_SIZE: int := 8

ghost function {:axiom} SpecCrcBytes(bytes: seq<byte>) : (result: seq<byte>)
    ensures |result| == CRC_SIZE

/// We make two assumptions about how CRCs can be used to detect
/// corruption.

/// The first assumption, encapsulated in
/// `Axiom_BytesUncorrupted`, is that if we store byte sequences
/// `x` and `y` to persistent memory where `y` is the CRC of `x`,
/// then we can detect an absence of corruption by reading both of
/// them. Specifically, if we read from those locations and get
/// `xCorrupted` and `yCorrupted` (corruptions of `x` and `y`
/// respectively), and `yCorrupted` is the CRC of `xCorrupted`,
/// then we can conclude that `x` wasn't corrupted, i.e., that
/// `xCorrupted == x`.

lemma {:axiom} Axiom_BytesUncorrupted(xCorrupted: seq<byte>, x: seq<byte>, xAddrs: seq<int>,
                                      yCorrupted: seq<byte>, y: seq<byte>, yAddrs: seq<int>)
    requires MaybeCorrupted(xCorrupted, x, xAddrs)
    requires MaybeCorrupted(yCorrupted, y, yAddrs)
    requires yCorrupted == SpecCrcBytes(xCorrupted)
    requires y == SpecCrcBytes(x)
    requires AllElementsUnique(xAddrs)
    requires AllElementsUnique(yAddrs)
    ensures x == xCorrupted

/// The second assumption, encapsulated in
/// `Axiom_CorruptionDetectingBoolean`, is that the values
/// `CDB_FALSE` and `CDB_TRUE` are so randomly different from each
/// other that corruption can't make one appear to be the other.
/// That is, if we know we wrote either `CDB_FALSE` or `CDB_TRUE`
/// to a certain part of persistent memory, and when we read that
/// same part we get `CDB_FALSE` or `CDB_TRUE`, we can conclude it
/// matches what we last wrote to it. To justify the assumption
/// that `CDB_FALSE` and `CDB_TRUE` are different from each other,
/// we set them to CRC(b"0") and CRC(b"1"), respectively.

const CDB_FALSE: uint64 := 0xa32842d19001605e // CRC(b"0")
const CDB_TRUE: uint64 := 0xab21aa73069531b7 // CRC(b"1")

lemma {:axiom} Axiom_CorruptionDetectingBoolean(cdbCorrupted: seq<byte>, cdb: seq<byte>, addrs: seq<int>)
    requires MaybeCorrupted(cdbCorrupted, cdb, addrs)
    requires AllElementsUnique(addrs)
    requires |cdb| == 8
    requires SpecDeserializeUint64(cdbCorrupted) == CDB_FALSE || SpecDeserializeUint64(cdbCorrupted) == CDB_TRUE
    requires SpecDeserializeUint64(cdb) == CDB_FALSE || SpecDeserializeUint64(cdb) == CDB_TRUE
    ensures  cdbCorrupted == cdb

const PERSISTENCE_CHUNK_SIZE: int := 8

ghost function UpdateBytes(s: seq<byte>, addr: int, bytes: seq<byte>) : seq<byte>
    requires 0 <= addr
    requires addr + |bytes| <= |s|
{
    seq(|s|, i requires 0 <= i < |s| => if addr <= i < addr + |bytes| then bytes[i - addr] else s[i])
}

ghost predicate AddrInChunk(chunk: int, addr: int)
{
    addr / PERSISTENCE_CHUNK_SIZE == chunk
}

/// We model writes as prophesizing which bytes will be written,
/// subject to the constraint that bytes in the same chunk
/// (aligned on `const_persistence_chunk_size()` boundaries) will
/// either all be written or have none of them written.

ghost predicate ChunkCorresponds(s1: seq<byte>, s2: seq<byte>, chunk: int)
{
    && |s1| == |s2|
    && (forall addr: int :: 0 <= addr < |s1| && AddrInChunk(chunk, addr) ==> s1[addr] == s2[addr])
}

ghost predicate ChunkTrigger(chunk: int)
{
    true
}

ghost predicate CanResultFromPartialWrite(post: seq<byte>, pre: seq<byte>, addr: int, bytes: seq<byte>)
{
    && 0 <= addr
    && addr + |bytes| <= |pre|
    && |post| == |pre|
    && (forall chunk: int {:trigger ChunkTrigger(chunk)} :: ChunkTrigger(chunk) ==> (
        || ChunkCorresponds(post, pre, chunk)
        || ChunkCorresponds(post, UpdateBytes(pre, addr, bytes), chunk)
    ))
}

datatype PersistentMemoryRegionView = PersistentMemoryRegionView(readState: seq<byte>, durableState: seq<byte>)

ghost predicate PmvValid(pmv: PersistentMemoryRegionView)
{
    |pmv.readState| == |pmv.durableState|
}

ghost function PmvLen(pmv: PersistentMemoryRegionView) : int
{
    |pmv.readState|
}

ghost predicate PmvCanResultFromWrite(pmv: PersistentMemoryRegionView, pre: PersistentMemoryRegionView, addr: int, bytes: seq<byte>)
{
    && 0 <= addr
    && addr + |bytes| <= PmvLen(pre)
    && PmvValid(pre)
    && PmvValid(pmv)
    && pmv.readState == UpdateBytes(pre.readState, addr, bytes)
    && CanResultFromPartialWrite(pmv.durableState, pre.durableState, addr, bytes)
}

ghost predicate PmvFlushPredicted(pmv: PersistentMemoryRegionView)
{
    pmv.durableState == pmv.readState
}

datatype PersistentMemoryConstants = PersistentMemoryConstants(imperviousToCorruption: bool)

class PermissionToControlWritesToPersistentMemory
{
    constructor Create()
      requires false
    {
    }
}

class PersistentMemoryRegion
{
    constructor Create()
        requires false
    {
    }

    ghost const constants: PersistentMemoryConstants

    ghost predicate Valid()
        reads this

    ghost function View() : PersistentMemoryRegionView
        reads this
        requires Valid()

    ghost function StatesPermitted() : iset<seq<byte>>
        reads this
        requires Valid()

    lemma {:axiom} Axiom_ImplicationsOfValid()
        requires Valid()
        ensures  PmvValid(View())
        ensures  View().durableState in StatesPermitted()

    method {:axiom} {:extern} GetRegionSize() returns (result: int64)
        requires Valid()
        ensures result as int == PmvLen(View())

    ghost method {:axiom} UpdateStatesPermitted(
        newStatesPermitted: iset<seq<byte>>,
        perm: PermissionToControlWritesToPersistentMemory
    )
        requires Valid()
        requires View().durableState in newStatesPermitted
        modifies this
        ensures  Valid()
        ensures  View() == old(View())
        ensures  StatesPermitted() == newStatesPermitted

    method {:axiom} {:extern} Read(addr: int64, bytes: array<byte>, offset: int32, numBytes: int32)
        requires Valid()
        requires 0 <= addr
        requires 0 <= offset
        requires 0 <= numBytes
        requires addr as int + numBytes as int <= PmvLen(View())
        requires offset as int + numBytes as int <= bytes.Length
        modifies bytes
        ensures  forall i: int :: 0 <= i < bytes.Length && !(offset as int <= i < offset as int + numBytes as int) ==>
                 bytes[i] == old(bytes[i])
        ensures  // If the persistent memory regions are impervious
                 // to corruption, read returns the last bytes
                 // written. Otherwise, it returns a
                 // possibly-corrupted version of those bytes.
                 var trueValues := View().readState[addr .. addr as int + numBytes as int];
                 var readValues := bytes[offset .. offset as int + numBytes as int];
                 var addrs := seq(numBytes, i => i as int + addr as int);
                 if constants.imperviousToCorruption then
                     readValues == trueValues
                 else
                     MaybeCorrupted(readValues, trueValues, addrs)

    method {:axiom} {:extern} Write(addr: int64, bytes: array<byte>, offset: int32, numBytes: int32)
        requires Valid()
        requires 0 <= offset
        requires 0 <= numBytes
        requires offset as int + numBytes as int <= bytes.Length
        requires 0 <= addr
        requires addr as int + numBytes as int <= PmvLen(View())
        requires // The caller must prove that all crash states are in `StatesPermitted()`
                 forall s: seq<byte> {:trigger s in StatesPermitted() } ::
                     CanResultFromPartialWrite(s, View().durableState, addr as int,
                                               bytes[offset .. offset as int + numBytes as int])
                     ==> s in StatesPermitted()
        modifies this
        ensures  Valid()
        ensures  StatesPermitted() == old(StatesPermitted())
        ensures  PmvCanResultFromWrite(View(), old(View()), addr as int,
                                       bytes[offset .. offset as int + numBytes as int])

    method {:axiom} {:extern} Flush()
        requires Valid()
        modifies this
        ensures  old(PmvFlushPredicted(View())) // it must have been prophesized that this flush would happen
        ensures  Valid()
        ensures  StatesPermitted() == old(StatesPermitted())
        ensures  View() == old(View())
}

}
