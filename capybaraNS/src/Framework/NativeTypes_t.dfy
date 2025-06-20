
module NativeTypesModule {
newtype{:nativeType "sbyte"} sbyte = i:int | -0x80 <= i < 0x80
newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
newtype{:nativeType "short"} int16 = i:int | -0x8000 <= i < 0x8000
newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
newtype{:nativeType "long"} int64 = i:int | -0x8000000000000000 <= i < 0x8000000000000000
newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000

newtype{:nativeType "sbyte"} nat8 = i:int | 0 <= i < 0x80
newtype{:nativeType "short"} nat16 = i:int | 0 <= i < 0x8000
newtype{:nativeType "int"} nat32 = i:int | 0 <= i < 0x80000000
newtype{:nativeType "long"} nat64 = i:int | 0 <= i < 0x8000000000000000

const SIZEOF_UINT64: int := 8
ghost function {:axiom} SpecSerializeUint64(value: uint64) : (result: seq<byte>)
    ensures |result| == 8
ghost function {:axiom} SpecDeserializeUint64(bytes: seq<byte>) : (result: uint64)
    requires |bytes| == 8
lemma {:axiom} Axiom_SerializeDeserializeUint64(value: uint64)
    ensures SpecDeserializeUint64(SpecSerializeUint64(value)) == value
lemma {:axiom} Axiom_DeserializeSerializeUint64(bytes: seq<byte>)
    requires |bytes| == 8
    ensures  SpecSerializeUint64(SpecDeserializeUint64(bytes)) == bytes

} 
