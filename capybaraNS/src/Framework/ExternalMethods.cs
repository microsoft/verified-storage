using System;
using System.Buffers.Binary;
using System.IO.Hashing;
using System.Security.Cryptography;
using NativeTypesModule;

namespace ExternalMethodsModule {
  
  public partial class ExternalMethods
  {
    static public void SerializeUint64(ulong value, byte[] outputBuffer, int start)
    {
        var span = new Span<byte>(outputBuffer, start, 8);
        BinaryPrimitives.WriteUInt64BigEndian(span, value);
    }

    static public ulong DeserializeUint64(byte[] bytes, int start)
    {
        var span = new ReadOnlySpan<byte>(bytes, start, 8);
        return BinaryPrimitives.ReadUInt64BigEndian(span);
    }
  }

  public partial class CrcDigest
  {
    Crc64 digest;

    CrcDigest(Crc64 i_digest)
    {
      digest = i_digest;
    }

    static public CrcDigest Create()
    {
      return new CrcDigest(new Crc64());
    }

    public void Add(byte[] bytes, int offset, int length)
    {
      digest.Append(new ReadOnlySpan<byte>(bytes, offset, length));
    }

    public void Compute(byte[] outputBuffer, int start)
    {
      var span = new Span<byte>(outputBuffer, start, 8);
      digest.GetCurrentHash(span);
    }

    public void Reset()
    {
      digest.Reset();
    }
  }

  public partial class KeyPair
  {
    RSA rsa;

    KeyPair(RSA i_rsa)
    {
      rsa = i_rsa;
    }

    static public KeyPair Generate()
    {
      RSA rsa = RSA.Create(2048);
      return new KeyPair(rsa);
    }

    static public KeyPair DeserializePrivateKey(byte[] bytes, int start, int length)
    {
      RSA rsa = RSA.Create();
      var span = new ReadOnlySpan<byte>(bytes, start, length);
      rsa.ImportRSAPrivateKey(span, out _);
      return new KeyPair(rsa);
    }

    public byte[] SerializePrivateKey()
    {
      return rsa.ExportRSAPrivateKey();
    }

    public byte[] SerializePublicKey()
    {
      return rsa.ExportRSAPublicKey();
    }

    public byte[] Sign(byte[] bytes, int start, int length)
    {
      var span = new ReadOnlySpan<byte>(bytes, start, length);
      return rsa.SignData(span, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
    }
  }

}
