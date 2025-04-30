include "NativeTypes_t.dfy"
include "PersistentMemory_t.dfy"

module ExternalMethodsModule {
import opened NativeTypesModule
import opened PersistentMemoryModule

class ExternalMethods
{
    static method {:axiom} {:extern} SerializeUint64(value: uint64, outputBuffer: array<byte>, start: int32)
        requires 0 <= start
        requires outputBuffer.Length >= start as int + SIZEOF_UINT64
        modifies outputBuffer
        ensures  outputBuffer[start .. start as int + SIZEOF_UINT64] == SpecSerializeUint64(value)
        ensures  forall i: int :: 0 <= i < start as int || start as int + SIZEOF_UINT64 <= i < outputBuffer.Length ==>
                 outputBuffer[i] == old(outputBuffer[i])

    static method {:axiom} {:extern} DeserializeUint64(bytes: array<byte>, start: int32) returns (result: uint64)
        requires 0 <= start
        requires bytes.Length >= start as int + SIZEOF_UINT64
        ensures  result == SpecDeserializeUint64(bytes[start .. start as int + SIZEOF_UINT64])
}

class CrcDigest
{
    ghost function {:axiom} View() : seq<byte>
        reads this

    static method {:axiom} {:extern} Create() returns (digest: CrcDigest)
        ensures fresh(digest)
        ensures digest.View() == []

    method {:axiom} {:extern} Add(bytes: array<byte>, start: int32, length: int32)
        requires 0 <= start
        requires 0 <= length
        requires start as int + length as int <= bytes.Length
        modifies this
        ensures  View() == old(View()) + bytes[start as int .. start as int + length as int]

    method {:axiom} {:extern} Compute(outputBuffer: array<byte>, start: int32)
        requires 0 <= start
        requires outputBuffer.Length >= start as int + CRC_SIZE
        ensures  outputBuffer[start .. start as int + CRC_SIZE] == SpecCrcBytes(View())
        ensures  forall i: int :: 0 <= i < start as int || start as int + CRC_SIZE <= i < outputBuffer.Length ==>
                 outputBuffer[i] == old(outputBuffer[i])

    method {:axiom} {:extern} Reset()
        modifies this
        ensures  View() == []
}

datatype KeyView = KeyView(publicKey: int, privateKey: int)

ghost predicate {:axiom} ValidKeyView(view: KeyView)
ghost predicate {:axiom} SpecKeyViewSerializationCorrect(view: KeyView, bytes: seq<byte>)
ghost function {:axiom} SpecDeserializeKeyView(bytes: seq<byte>) : KeyView
ghost predicate {:axiom} SpecPublicKeySerializationCorrect(key: int, bytes: seq<byte>)
lemma {:axiom} Axiom_SerializeDeserializeKeyView(view: KeyView, bytes: seq<byte>)
    ensures SpecKeyViewSerializationCorrect(view, bytes) ==> view == SpecDeserializeKeyView(bytes)

ghost predicate {:axiom} SpecSignCorrect(privateKey: int, bytes: seq<byte>, signature: seq<byte>)

class KeyPair
{
    ghost function {:axiom} View() : KeyView

    static method {:axiom} {:extern} Generate() returns (keyPair: KeyPair)
        ensures fresh(keyPair)
        ensures ValidKeyView(keyPair.View())

    static method {:axiom} {:extern} DeserializePrivateKey(bytes: array<byte>, start: int32, length: int32) returns (keyPair: KeyPair)
        requires 0 <= start
        requires 0 <= length
        requires start as int + length as int <= bytes.Length
        requires ValidKeyView(SpecDeserializeKeyView(bytes[start as int .. start as int + length as int]))
        ensures  SpecDeserializeKeyView(bytes[start .. start as int + length as int]) == keyPair.View()

    method {:axiom} {:extern} SerializePrivateKey() returns (result: array<byte>)
        requires ValidKeyView(this.View())
        ensures  SpecKeyViewSerializationCorrect(this.View(), result[..])
        ensures  result.Length <= 0x7FFF_FFFF

    method {:axiom} {:extern} SerializePublicKey() returns (result: array<byte>)
        requires ValidKeyView(this.View())
        ensures  SpecPublicKeySerializationCorrect(this.View().publicKey, result[..])
        ensures  result.Length <= 0x7FFF_FFFF

    method {:axiom} {:extern} Sign(bytes: array<byte>, start: int32, length: int32) returns (signature: array<byte>)
        requires ValidKeyView(this.View())
        requires 0 <= start
        requires 0 <= length
        requires start as int + length as int <= bytes.Length
        ensures  SpecSignCorrect(this.View().privateKey, bytes[start .. start as int + length as int], signature[..])
        ensures  signature.Length <= 0x7FFF_FFFF
}

}
