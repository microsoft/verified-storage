# About

This directory contains the files needed to replicate experiments concerning
the verified notary service called CapybaraNS. These experiments come from the
OSDI 2025 paper "PoWER Never Corrupts: Tool-Agnostic Verification of Crash
Consistency and Corruption Detection" by Hayley LeBlanc, Jacob R. Lorch, Chris
Hawblitzel, Cheng Huang, Yiheng Tao, Nickolai Zeldovich, and Vijay
Chidambaram.

To check that the code untrusted code verifies, see [Verification and
Compilation](#verification-and-compilation). To check that the line counts
reported in the paper are correct, see [Computing Code
Size](#computing-code-size). If one wants to manually audit that CapybaraNS
has a PoWER-based specification that ensures crash consistency, see [Manual
Auditing](#manual-auditing).

# Setup

To replicate our results, you'll need the following tools:
  * .NET 8.0 SDK (available at `https://dotnet.microsoft.com/download`)
  * Dafny v4.10.0 (available at `https://github.com/dafny-lang/dafny`)
  * Python 3
  * scons (installable by running `pip3 install scons`)
  * sloccount (available at `https://dwheeler.com/sloccount/`)
    
The instructions below have been tested using Windows 11 and Ubuntu 20.04.
They should also work for other platforms Dafny and .NET support, such as
macOS, Ubuntu 16.04, and Debian. On Windows 11, they work with at least the
Command Prompt, PowerShell 5.1, and Windows Subsystem for Linux. However,
there is one exception: the instructions for computing code size don't work on
Windows native, so on that platform one must use the Windows Subsystem for
Linux.

# Verification and Compilation

To verify and build the contents of this repo, use the following command from
this directory (the one with this `README.md` in it):

```
scons --dafny-path=/path/to/directory/with/dafny/
```
Please provide a full absolute path to your Dafny installation. Paths including `~/` may not work.

To use `<n>` threads in parallel, add `-j <n>` to this command.

Expect this to take under a minute, depending on your machine and how many
cores you have available.  Also note that the prover's time limits are based on
wall clock time, so if you run the verification on a slow machine, you may see a
few timeouts not present in our build.  If that happens, try using a longer time
limit for each verification; for example, using `--time-limit=120` makes the time
limit 120 seconds instead of the default 60 seconds.

Running `scons` will produce an executable in the subdirectory `bin` named
`NotaryServer` (or, on Windows, `NotaryServer.exe`).

To produce this executable without performing verification, add the argument
`--no-verify` to the `scons` command.

**Expected output**: If verification and compilation succeed, you will see a message that says "Build succeeded" with 0 warnings or errors. You will also see lines like "Dafny program verifier finished with 10 verified, 0 errors" for each file. Note that the build system will not rebuild/re-verify the system again unless you first run `scons -c --dafny-path=...` to clean up the binary and build artifacts.


# Computing Code Size

The script for computing code size won't work on Windows (but will work in the
Windows Subsystem for Linux). It assumes that the sloccount and Dafny
executables are on your path as `sloccount` and `dafny` respectively. It uses
the `dafny` tool to distinguish what code is trusted vs. spec+proof vs.
implementation, and uses the `sloccount` tool to count lines of code. Since
`sloccount` does not directly operate on Dafny files, but Dafny is similar in
structure to C#, the script gives Dafny files a `.cs` suffix before running
`sloccount` on them.

To execute it, run the following from this directory (the one with this
`README.md` in it):
```
python3 dafny-line-count.py
```

This will produce standard output in text and then in LaTeX; the LaTeX content
is also saved to a file named `notary-line-counts.tex`. The LaTeX content
should match the contents for the CapybaraNS part of Table 3 in the paper.

# Manual Auditing

The untrusted code, which is verified using Dafny, consists of various files
ending in `_v.dfy` where the `v` stands for "verified". You don't have to read
these files to have confidence in the correctness of the system; you just need
to have Dafny verify them, as described in the [Verification and
Compilation](#verification-and-compilation) section above. The other code
files, i.e., the Dafny files ending in `_t.dfy` and the C# files which end in
`.cs`, need to be read and understood to audit the system properly.

That said, the only file whose auditing is really relevant to the topic of the
OSDI 2025 paper is `TrustedNotary_t.dfy`. That file shows how one can use the
PoWER approach to implement a trusted API that ensures crash consistency even
though it uses an untrusted verified component.

For those interested in auditing all the untrusted files, even those not
relevant to the research results, those files fall into three categories: (1)
Trusted code in the `Framework` directory provides wrappers for
framework-provided functionality like cryptographic operations and simulating
persistent memory with files. (2) C# files in the `NotaryServer` directory
provide the untrusted client and the bootstrapping functions for launching the
server. (3) Trusted Dafny files in the `NotaryServer` directory describe the
notary service specification (in `NotarySpec_t.dfy`) and the above-mentioned
PoWER-based wrapper that ensures crash consistency for the service (in
`TrustedNotary_t.dfy`).

# Running

Running the notary server executable with no parameters produces a help
message describing its usage. Here is more explanation of that usage.

The notary server executable is actually a combination of a test client and a
notary server. There are two modes you can run the executable in: setup and
start. Setup creates a file to store persistent state in, using that file as a
simulation of persistent memory. Start recovers from an existing file, and
runs a simple test sequence of operations on that file. Those operations are:
(1) advance the counter with a random message, (2) advance the counter with a
second random message, (3) sign the most recently used message, and (4) test
that the signature is valid.

To perform setup, use a command like the following:
```
./bin/NotaryServer setup=true filename=mytestfile.txt
```

To start, use a command like the following:
```
./bin/NotaryServer setup=false filename=mytestfile.txt
```

You can start multiple times in a row, and each time it will reflect all the
operations performed in previous runs (since they persist). To reset the
persistent state, run setup again.

**Expected output:**
Running the notary server with `setup=true` should output:
```
Notary Server is starting...
Notary Server file set up successfully.
Notary Server is running.
```

Running with `setup=false` should output: 
```
Notary Server is starting...
Notary Server started successfully.
Signature has length 256
Counter is 2
Signature is verified.
Notary Server is running.
```
