include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"
include "../Framework/PmemUtil_v.dfy"
include "Layout_v.dfy"
include "NotarySpec_t.dfy"

module NotaryUtilModule {
import opened ExternalMethodsModule
import opened PersistentMemoryModule
import opened PmemUtilModule
import opened NativeTypesModule
import opened NotaryLayoutModule
import opened NotarySpecModule

method ZeroRange(bytes: array<byte>, start: int32, length: int32)
    requires 0 <= start
    requires 0 <= length
    requires start as int + length as int <= bytes.Length
    requires start as int + length as int <= 0x7FFF_FFFF
    modifies bytes
    ensures  bytes[start as int .. start as int + length as int] == SequenceOfZeroes(length as int)
    ensures  forall i: int :: 0 <= i < start as int || start as int + length as int <= i < bytes.Length ==>
             bytes[i] == old(bytes[i])
{
    var j := start;
    while j < start + length
        invariant start <= j <= start + length
        invariant forall i: int :: 0 <= i < start as int || start as int + length as int <= i < bytes.Length ==> bytes[i] == old(bytes[i])
        invariant forall i: int :: start as int <= i < j as int ==> bytes[i] == 0
        modifies bytes
    {
        bytes[j] := 0;
        j := j + 1;
    }
}

method CopyArray(dest: array<byte>, src: array<byte>, startDest: int32, startSrc: int32, length: int32)
    requires 0 <= startDest
    requires 0 <= startSrc
    requires 0 <= length
    requires startDest as int + length as int <= dest.Length
    requires startSrc as int + length as int <= src.Length
    requires startDest as int + length as int <= 0x7FFF_FFFF
    requires startSrc as int + length as int <= 0x7FFF_FFFF
    requires dest != src
    modifies dest
    ensures  dest[startDest as int .. startDest as int + length as int] == src[startSrc as int .. startSrc as int + length as int]
    ensures  forall i: int :: 0 <= i < startDest as int || startDest as int + length as int <= i < dest.Length ==>
             dest[i] == old(dest[i])
{
    var j := 0;
    while j < length
        invariant 0 <= j <= length
        invariant forall i: int {:trigger dest[startDest as int .. startDest as int + length as int][i]} :: 0 <= i < j as int ==>
                  dest[startDest as int .. startDest as int + length as int][i] == src[startSrc as int .. startSrc as int + length as int][i]
        invariant forall i: int :: 0 <= i < startDest as int || startDest as int + length as int <= i < dest.Length ==>
                  dest[i] == old(dest[i])
        modifies dest
    {
        dest[startDest + j] := src[startSrc + j];
        j := j + 1;
    }
}

method CompareArrays(a1: array<byte>, a2: array<byte>, start1: int32, start2: int32, length: int32) returns (equal: bool)
    requires 0 <= start1
    requires 0 <= start2
    requires 0 <= length
    requires a1.Length <= 0x7FFF_FFFF
    requires a2.Length <= 0x7FFF_FFFF
    requires start1 as int + length as int <= a1.Length
    requires start2 as int + length as int <= a2.Length
    ensures  equal <==> a1[start1 .. start1 as int + length as int] == a2[start2 .. start2 as int + length as int]
{
    var j: int32 := 0;
    while j < length
        invariant 0 <= j <= length
        invariant forall i: int {:trigger a1[start1 .. start1 as int + length as int][i]} :: 0 <= i < j as int ==>
                  a1[start1 .. start1 as int + length as int][i] == a2[start2 .. start2 as int + length as int][i]
    {
        if a1[start1 + j] != a2[start2 + j] {
            assert(a1[start1 .. start1 as int + length as int][j] != a2[start2 .. start2 as int + length as int][j]);
            return false;
        }
        j := j + 1;
    }

    assert a1[start1 .. start1 as int + length as int] == a2[start2 .. start2 as int + length as int];
    return true;
}

lemma Lemma_SubrangeOfSubrange(s: seq<byte>, outerRangeStart: int, outerRangeEnd: int, innerRangeStart: int, innerRangeEnd: int)
    requires 0 <= outerRangeStart <= innerRangeStart <= innerRangeEnd <= outerRangeEnd <= |s|
    ensures  s[innerRangeStart .. innerRangeEnd] ==
             s[outerRangeStart .. outerRangeEnd][innerRangeStart - outerRangeStart .. innerRangeEnd - outerRangeStart]
{
    var s1 := s[innerRangeStart .. innerRangeEnd];
    var s2 := s[outerRangeStart .. outerRangeEnd][innerRangeStart - outerRangeStart .. innerRangeEnd - outerRangeStart];
    var len := innerRangeEnd - innerRangeStart;
    assert |s1| == |s2| == len;
    forall j: int | 0 <= j < len
        ensures s1[j] == s2[j]
    {
        assert s1[j] == s[innerRangeStart + j] == s2[j];
    }
}

lemma Lemma_SubrangeOfSubrangeForall(s: seq<byte>, outerRangeStart: int, outerRangeEnd: int)
    requires 0 <= outerRangeStart <= outerRangeEnd <= |s|
    ensures  forall innerRangeStart: int, innerRangeEnd: int {:trigger s[innerRangeStart .. innerRangeEnd]} ::
                 outerRangeStart <= innerRangeStart <= innerRangeEnd <= outerRangeEnd ==>
                 s[innerRangeStart .. innerRangeEnd] ==
                 s[outerRangeStart .. outerRangeEnd][innerRangeStart - outerRangeStart .. innerRangeEnd - outerRangeStart]
{
    forall innerRangeStart: int, innerRangeEnd: int {:trigger s[innerRangeStart .. innerRangeEnd]}
        | outerRangeStart <= innerRangeStart <= innerRangeEnd <= outerRangeEnd
        ensures s[innerRangeStart .. innerRangeEnd] ==
                s[outerRangeStart .. outerRangeEnd][innerRangeStart - outerRangeStart .. innerRangeEnd - outerRangeStart]
    {
        Lemma_SubrangeOfSubrange(s, outerRangeStart, outerRangeEnd, innerRangeStart, innerRangeEnd);
    }
}

}
