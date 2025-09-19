using PersistentMemoryModule;
using System;
using System.Buffers.Binary;
using System.Security.Cryptography;
using TrustedNotaryModule;

namespace NotaryServer
{
    class Program
    {
        static void usage()
        {
          Console.Write(@"
Usage:  NotaryServer.exe [key=value]...

Allowed keys:
  filename       - file name to use for storage to enable crash recovery
  setup          - set up a new notary service instead of restarting an
                   existing one that crashed (false or true, default false)
  verbose        - print verbose output (false or true, default false)
");
    }

        static void TestNotary(TrustedNotary notaryServer)
        {
            var publicKey = notaryServer.ExtractPublicKey();
            var message = new byte[32];
            var rng = new Random();
            rng.NextBytes(message);
            var success = notaryServer.Advance(message);
            if (!success) {
                Console.WriteLine("Notary Server failed to advance the first time.");
                return;
            }
            rng.NextBytes(message);
            success = notaryServer.Advance(message);
            if (!success) {
                Console.WriteLine("Notary Server failed to advance the second time.");
                return;
            }
            var signature = notaryServer.Sign();
            Console.WriteLine("Signature has length {0}", signature.Length);
            var counter = notaryServer.ReadCounter();
            Console.WriteLine("Counter is {0}", counter);

            byte[] data = new byte[8 + message.Length];
            BinaryPrimitives.WriteUInt64BigEndian(new Span<byte>(data, 0, 8), counter);
            message.CopyTo(data, 8);

            var rsa = RSA.Create();
            rsa.ImportRSAPublicKey(publicKey, out _);
            var verified = rsa.VerifyData(data, signature, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
            if (verified) {
                Console.WriteLine("Signature is verified.");
            }
            else {
                Console.WriteLine("Signature is not verified.");
            }
        }

        static void Main(string[] args)
        {
           Params ps = new Params();

           foreach (var arg in args)
           {
             if (!ps.ProcessCommandLineArgument(arg)) {
               usage();
               return;
             }
           }

           if (!ps.Validate()) {
             usage();
             return;
           }

            Console.WriteLine("Notary Server is starting...");
            if (ps.Setup) {
                var requiredFileSize = TrustedNotaryModule.TrustedNotary.GetRequiredFileSize();
                var fileHandle = PersistentMemoryModule.PersistentMemoryRegion.Create(ps.FileName, requiredFileSize);
                var perm = new PermissionToControlWritesToPersistentMemory();
                var success = TrustedNotaryModule.TrustedNotary.Setup(fileHandle, perm);
                if (success) {
                    Console.WriteLine("Notary Server file set up successfully.");
                }
                else {
                    Console.WriteLine("Notary Server file setup failed.");
                }
            }
            else {
                var fileHandle = new PersistentMemoryModule.PersistentMemoryRegion(ps.FileName);
                var perm = new PermissionToControlWritesToPersistentMemory();
                var trustedNotary = TrustedNotaryModule.TrustedNotary.Start(fileHandle, perm);
                if (trustedNotary != null) {
                    Console.WriteLine("Notary Server started successfully.");
                    TestNotary(trustedNotary);
                }
                else {
                    Console.WriteLine("Notary Server failed to start.");
                }
            }
            // Initialize server components here
            // Start server logic here
            Console.WriteLine("Notary Server is running.");
        }
    }
}
