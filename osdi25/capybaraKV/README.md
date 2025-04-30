# About

This directory contains the files needed to replicate experiments concerning
the verified key-value store called CapybaraKV. These experiments come from the
OSDI 2025 paper "PoWER Never Corrupts: Tool-Agnostic Verification of Crash
Consistency and Corruption Detection" by Hayley LeBlanc, Jacob R. Lorch, Chris
Hawblitzel, Cheng Huang, Yiheng Tao, Nickolai Zeldovich, and Vijay
Chidambaram.

## Table of contents
1. [Recommended setup](#recommended-hardware-and-os)
2. [Outline](#outline)
3. [Setup](#setup-instructions-30-minutes)
4. [Verification](#verification-5-minutes)
5. [Manual auditing](#manual-auditing)
6. [Performance experiments](#performance-experiments)
7. [Processing data](#processing-data)
8. [Claims and expected results](#claims-and-expected-results) 
9. [Notes and troubleshooting](#notes-and-troubleshooting)
   1. [Emulated PM](#emulated-pm)
   2. [Optane PM](#optane-pm)
   3. [Troubleshooting](#troubleshooting)

### Recommended hardware and OS

The experiments described here were run on the following setup:
* 128 GiB Intel Optane DC Persistent Memory Module (one non-interleaved NVDIMM)
* 128 GiB DRAM
* Debian Trixie (Linux kernel v6.12.10)
* 2-socket Intel Xeon Silver processor with 32 physical cores

A server with this setup can be made available to artifact evaluators upon request.

We recommend adhering to the described hardware setup as closely as possible. 
In particular, using Optane PM rather than emulated PM is ideal, as they have very different performance profiles.
However, our code does support running experiments on emulated PM, and we describe expected differences below.
The original experiments were run on the setup described above. We have also tested the setup instructions and kick-the-tires tests on:
- Ubuntu Jammy with 64GiB emulated PM and 128GiB Optane PM
- Ubuntu Noble with 64GiB emulated PM

### Outline

There are five main steps to evaluate the CapybaraKV part of this artifact.
For artifact evaluators, we recommend running steps 1-3 during the kick-the-tires phase.

1. Set up the chosen evaluation machine. We provide a script to install/build all required dependencies. This takes about 15-30 minutes.
2. Verify CapybaraKV and check its line counts. We provide scripts to run verification and calculate line counts. This should take 5-10 minutes.
3. Run the provided ["mini" benchmarks](#suggested-kick-the-tires-tests) to check that everything works as expected. We provide scripts and configuration files for these experiments. It should take less than 30 minutes to run these.
4. Run the full performance experiments and generate plots/tables corresponding to those in the paper. We provide scripts and and configuration files for these experiments. **TODO timing**
5. Optionally, manually auditing CapybaraKV's specification. We provide a guide for auditing in [Manual auditing](#manual-auditing). This step does not require running any code and can be done concurrently with step 4. 

**All instructions in this document assume you are starting from `verified-storage/osdi25/capybaraKV`.**
Note that the `setup.sh` script downloads/clones some dependencies as siblings of `verified-storage/`. 

We recommend running the evaluation in a `tmux` or `screen` session, as many steps take a while to run.

### Setup instructions (~15-30 minutes)

1. Install `git`: `sudo apt install git`
2. Clone this repository: `git clone -b kv2 --single-branch https://github.com/microsoft/verified-storage.git`.
3. `cd evaluation` and run `./setup.sh`. You may be prompted to enter a password for `sudo` partway through the script. This script will: 
   1. Install `apt` dependencies for other key-value stores
   2. Install Rust
      1. **Note**: If you're using the provided PM machine, you may see errors about `$HOME` being different from the euid-obtained home directory. These errors don't impact installation and can safely be ignored.
   3. Build the crates in the `verified-storage` repo
   4. Clone Verus into a sibling of the `verified-storage` directory, build it, and add it to your `PATH`. 
   5. Download Maven as a sibling of the `verified-storage` directory and add it to your `PATH`.
   6. Build the other KV stores (pmem-Redis, pmem-RocksDB, and Viper) and their dependencies
   7. Build YCSB bindings for all KV stores
4. **Create a directory `/mnt/pmem/` to mount a PM file system on for experiments. Do not name this directory something else -- one of the systems we compare against has this path hardcoded in.**
5. **If you are using emulated PM**: Follow the instructions in [Emulated PM](#emulated-pm) to set up the emulated persistent memory. 
6. Check that your PM is set up correctly and ensure it is in non-interleaved `fsdax` mode. `ls /dev | grep pmem` should return at least one line of output like `pmem0`. The output of `lsblk` should include that device and that its size matches that of a single NVDIMM installed in the machine . If you are using real PM and the output of either command does not look correct, refer to [Optane PM](#optane-pm). Emulated PM should be set up correctly automatically.

After running `setup.sh`, run `source ~/.bashrc` to ensure new additions are reflected in your `PATH` variable.

The `setup.sh` script will exit immediately if any steps fail, and can safely be re-run to complete an interrupted setup process.

The rest of these instructions assume that this script is used to prepare the system to use the artifact.

### Verification (~5 minutes)

#### Verifying CapybaraKV

To verify CapybaraKV and collect verification time metrics:
1. `cd` to `capybarakv/src` 
2. Run the following commands:
```bash
./verify-ae.sh --time --num-threads 1 # runs verification with one thread
./verify-ae.sh --time --num-threads 8 # runs verification with eight thread
```

The script will store output from verification in `capybarakv/src/verif_output_{timestamp}.txt` and print the main metrics (verification results and time) to the terminal.
If everything worked as expected, the output will include a line like `verification results:: 707 verified, 0 errors`.

**Note**: In the `verif_output.txt` file, you may see messages like "function body check finished in 2 seconds" or "Some checks are taking longer than 2s", particularly in the 1 thread case. These are unrelated to the verification results and can be ignored.

**Note**: We've observed different verification times on different machines, so some variation is expected.
The following table reports total verification time on several different machines to give a sense of the amount of variation we expect to see.
All Intel CPUs are running recent versions of Debian or Ubuntu unless otherwise noted.

| Machine details                                                                            | 1 thread    | 8 threads  |
| ------------------------------------------------------------------------------------------ | ----------- | ---------- |
| 11th Gen Intel Core i7-11850H @ 2.50GHz, 16 cores (8 physical), 32GiB RAM                  | 54 seconds  | 23 seconds |
| Intel Core i9-10885H @ 2.40GHz, 16 cores (8 physical), 64GiB RAM, Windows 11 in PowerShell | 125 seconds | 41 seconds |
| Intel Xeon Silver 4314 CPU @ 2.40GHz, 64 cores (32 physical), 128GiB RAM                   | 92 seconds  | 28 seconds |
| Intel Xeon Gold 6242 CPU @ 2.80GHz, 64 cores (32 physical), 192 GiB RAM                    | 98 seconds  | 30 seconds |
| Intel Xeon Gold 6126 CPU @ 2.60GHz, 48 cores (24 physical), 192 GiB RAM                    | 97 seconds  | 32 seconds |
| Apple M1 Max, 10 cores, 64 GiB RAM                                                         | 48 seconds  | 16 seconds |



#### Computing Code Size (~1 minute)

We use Verus' built-in line-counting tool to count lines of code and categorize them as trusted, specification/proof, or executable. 
We provide a python script, `count_capybarakv_lines.py`, that uses this tool to generate a table of line counts and a proof-to-code ratio for CapybaraKV.
The script also uses `tokei` (https://github.com/XAMPPRocky/tokei, installed by `setup.sh`) to count the lines of code in the `pmcopy` crate, which is implemented in regular Rust.

1. From `capybarakv/src`, run `./verify-ae.sh --emit=dep-info`. This will generate a `lib.d` file in that directory.
2. In the same directory, run `python3 count_capybarakv_lines.py lib.d ../../pmcopy ../../../../../verus`. This will generate a table matching the CapybaraKV portion of Table 3 as well as the proof-to-code ratio based on line counts in the table.
3. This script will output a table that looks similar to Table 3 in the paper. The values in the table and the proof-to-code ratio reported under the outputted table should match those in the paper.

### Manual auditing

To gain confidence that what is being verified is indeed a reasonable specification of correctness for a key/value store, you may decide to audit the unverified parts of the code.
All of the files referred to in this section are in `capybarakv/src` except for the `pmcopy` crate, which has its source code in `pmcopy/src`.

The untrusted code, which is verified by Verus, consists of various files ending in `_v.rs`, where the `v` stands for "verified". You don't have to read these files to have confidence in the correctness of the system; you just need to have Verus verify them, as described above. The other code files, i.e., the files ending in `_t.rs`, need to be read and understood to audit the system properly.

That said, the only files whose auditing are really relevant to the main topic of the OSDI 2025 paper are:
* `kv2/impl_t.rs`, the top-level API for CapybaraKV, which shows how one can use the PoWER approach to implement a trusted single-threaded API that ensures crash consistency even though it uses an untrusted verified component;
* `pmem/pmemspec_t.rs`, which has our prophecy-based model of persistent memory;
* `pmem/power_t.rs`, which provides data structures for writing PoWER specifications; and
* `pmem/power_sound_t.rs`, which demonstrates that satisfying a PoWER specification implies the satisfaction of an atomic invariant.

For those interested in auditing all the untrusted files, even those less relevant to the research results, those files fall into two categories: (1) The `pmem` directory contains framework-provided functionality including modeling of persistent memory and the crash and corruption behavior thereof. (2) Trusted Verus files in the `kv2` directory describe the key/value service specification (`spec_t.rs`); the PoWER-based wrapper that ensures crash consistency for the single-threaded version of the service (`impl_t.rs`); and files that specify concurrent versions of the service (`concurrentspec_t.rs`, `rwkv_t.rs`, and `shardkv_t.rs`).

Our design enables the use of the same untrusted verified component for single-threaded and multi-threaded versions, `UntrustedKvStoreImpl`. The single-threaded version, in `kv2/impl_t.rs`, upon startup supplies the `UntrustedKvStoreImpl` with a blanket permission permitting it to do arbitrary mutations to storage as long as they don't affect the post-recovery state. This permission is all that's needed to support all operations except `commit`, since `commit` is the only operation that's permitted to change the post-recovery state. For `commit`, `kv2/impl_t.rs` provides a single-use permission allowing the untrusted KV store to transition from the pre-commit state to the post-commit state.

As discussed in the paper, we have a Verus library that exposes the PoWER interface but enforces an atomic invariant about the storage state. This serves two purposes. First, the existence of this library demonstrates that satisfying a PoWER specification implies the satisfaction of an atomic invariant. Second, we can use it to build a KV store satisfying a concurrent specification, leveraging the untrusted component `UntrustedKvStoreImpl` that was designed with a PoWER interface. To audit the first claim, read `pmem/power_sound_t.rs`. To audit the second claim, read the specifications for the concurrent KV stores. These specifications, unlike the one for the single-threaded KV store, do not expose transactions; rather, they describe various read-only and mutating operations that can be done atomically. For each mutating operation, its API has the caller supply a `MutatingLinearizer`, which gives a proof-mode callback to be called by the KV store atomically with the commit point of the operation.

As discussed in the paper, we have two concurrent KV stores satisfying the specification in `kv2/concurrent_spec_t`. One, specified in `kv2/rwkv_t.rs`, uses a multiple-readers/single-writer lock to allow concurrent reads but not concurrent writes. The other, specified in `kv2/shardkv_t.rs`, uses sharding by key hash to allow concurrent writes to keys occupying different shards. None of these files needs to be audited for proper use of PoWER since they use PoWER internally, in `_v.rs` files that don't needed to be trusted. That is, they leverage our library to use PoWER to establish an atomic invariant, which is in turn used to call mutating callbacks at provably appropriate times.

### Performance experiments

There are two main performance experiments: a set of microbenchmarks and a set of macrobenchmarks.
The full experiments take a long time to run, so each experiment has a mini kick-the-tires setup that runs quickly to check that everything is working as well as a set of suggested full experiment configuration options.

All experiments require a mount point and a PM device to use. 
These instructions (and the default configurations) use `/mnt/pmem` and `/dev/pmem0`, respectively.
These instructions (and default configs) place all results in `evaluation/results/artifact-evaluation`.

#### Suggested kick-the-tires tests (~15 minutes)

These instructions explain how to run the mini version of experiments and check that their output looks reasonable.

##### Mini microbenchmarks (~3 minutes)
The kick-the-tires version of this experiment runs our latency experiments on each KV store with a small number (25000) of records.
To run this version, run the following commands:
```bash
cd evaluation/benchmark
cargo run --release -- ../configs/mini_microbenchmark_config.toml
```

The results from each system will be organized by system and operation under `evaluation/results/artifact-evaluation/microbenchmark`. 
There should be one file named `Run1` in each directory. 
Each line of each of these files should contain one latency measurement.

**Note**: running the microbenchmark code will output a lot of warnings. These are from RocksDB and can be ignored.

**Note**: You may have issues with typed input not appearing in your terminal after running this experiment. We have found that Redis can mess up the terminal in a way that hides input. You can type `reset` (you won't be able to see it), then hit Enter to reset the terminal and bring it back to normal; note that this will also clear the terminal output from the experiment.

##### Mini macrobenchmarks (~5-10 minutes)
The kick-the-tires version of this experiment runs several small YCSB experiments.
It runs workloads {Load,Run}A and {Load,Run}X on each evaluated system with 10000 records with 1 and 16 threads
To run this version, run the following commands:
```bash
cd evaluation
./run_ycsb_mini.sh
```
This script uses configuration files in `configs/` to set up experiments. 
To change these configurations (e.g., to change results directory or mountpoint/PM device) see the instructions for the `update_configs.sh` script below in [Changing configurations](#changing-configurations).

After running these experiments, `results/` contain two directories, `threads1` and `threads16`. Each of those contains a directory for each evaluated system; the directory for each system should contain directories `Load{a,e,x,y,z}` and `Run{a,b,c,d,f,x,y,z}`. Only `Load{a,x}` and `Run{a,x}` directories will contain anything; each should contain one file that looks something like this:
```bash
Pre-experiment available mem: 130744803328
Post-experiment available mem: 130736324608
Mem usage: 8478720
[OVERALL], RunTime(ms), 35
[OVERALL], Throughput(ops/sec), 28571.428571428572
[TOTAL_GCS_G1_Young_Generation], Count, 0
[TOTAL_GC_TIME_G1_Young_Generation], Time(ms), 0
[TOTAL_GC_TIME_%_G1_Young_Generation], Time(%), 0.0
[TOTAL_GCS_G1_Old_Generation], Count, 0
[TOTAL_GC_TIME_G1_Old_Generation], Time(ms), 0
[TOTAL_GC_TIME_%_G1_Old_Generation], Time(%), 0.0
[TOTAL_GCs], Count, 0
[TOTAL_GC_TIME], Time(ms), 0
[TOTAL_GC_TIME_%], Time(%), 0.0
... // truncated additional information about individual operations like INSERT, READ, etc.
```
There will be some additional storage usage information in CapybaraKV-related files.
If all of these files exist and have contents of this form, the kick-the-tires experiment succeeded.
Note that the experiments did not run long enough to obtain accurate performance results, so the average throughput in these files will be very different from what is reported in the paper.

#### Full experiments

If you're able to run the kick-the-tires tests successfully, you should now be able run the full experiments described here.

The full experiments we ran for the paper take a long time to run because we ran the microbenchmarks on a large number of keys and the macrobenchmarks multiple times to reduce noise.
Using fewer keys in the microbenchmarks and fewer iterations in the macrobenchmarks may result in more noise but takes much less time, so we suggest that artifact evaluators use 5M keys in the microbenchmarks and 1 iteration of each macrobenchmark.

The default configuration files use these settings; if you would like to do multiple iterations, see [Changing configurations](#changing-configurations) for instructions on updating these files.
The timing estimates we provide here are based on these default configurations running on 128GiB Optane PM.

##### Microbenchmarks (~4 hours)

The Rust crate at `evaluation/benchmark` runs our microbenchmarks (Figure 2) and collects startup times ("Mount time" columns in Table 4).

To run these experiments on a device 128GiB or larger, run:
```bash
cd evaluation/benchmark
cargo run --release -- ../configs/microbenchmark_config_128GB.toml
```
We also provide a configuration file for 64GiB of PM; replace `128GB` with `64GB` to use it.

**Note:** If you've already run the kick-the-tires tests, that data will be overwritten by data from this experiment.

##### YCSB macrobenchmarks and memory/storage utilization (~6 hours on DRAM, TODO on PM)
 
The data presented in the paper is the average from five iterations of each YCSB workload on each system; collecting this data takes several days, so we suggest that artifact evaluators collect data from a single iteration.
The provided config files use 1 iteration as the default.

To run the full macrobenchmark, run:
```bash
cd evaluation
./run_ycsb.sh
```
This script runs YCSB workloads based on the config files mentioned above in [Performance Experiments](#performance-experiments).
These experiments will collect throughput data as well as memory and storage utilization on several workloads and place it in the `evaluation/results/artifact-evaluation` directory (or the directory set using `update_configs.sh`).

### Processing data

We provide scripts to process data and output the graphs and tables seen in the paper.


#### Microbenchmark data

##### Figure 2

After running the full microbenchmarks, use the following to generate Figure 2.
```bash
cd evaluation
python3 plot_fig2.py results/artifact_evaluation_results/microbenchmark
```
The first time it runs, it will save the results in a JSON file called `results.json`. 
If you need to re-create the plot on the same data, you can use `python3 plot_fig2.py results/artifact_evaluation_results/microbenchmark -r` to have the script read from `results.json` instead of recalculating everything from scratch.

#### Macrobenchmark data

Use the following commands to parse and plot data from the YCSB macrobenchmark.

##### Figure 3
These commands should only be run after the full macrobenchmarks have completed.
```bash
cd evaluation

# parse the YCSB output into CSVs with the average overall throughput from each run
# usage: python3 parse_ycsb.py <num kvs> <kv1> <kv2> ... <num runs> <first run id> <results dir> <output csv>
python3 parse_ycsb.py 4 redis pmemrocksdb viper capybarakv 1 1 results/artifact_evaluation_results/threads_1 ycsb_1thread.csv
python3 parse_ycsb.py 4 redis pmemrocksdb viper capybarakv 1 1 results/artifact_evaluation_results/threads_16 ycsb_16thread.csv

# plot the YCSB results and output into ae_ycsb_output.pdf
# usage: python3 plot_fig3.py <1 thread csv> <16 thread csv> <output pdf>
python3 plot_fig3.py ycsb_1thread.csv ycsb_16thread.csv figure3.pdf
```

##### Figure 4
Note: this script does its own parsing, so it does not use parse_ycsb.py, which is only used to handle data from multiple KV stores.

This command should only be run after the full macrobenchmarks have completed.

```bash
cd evaluation
# usage: python3 plot_fig4.py <num runs> <first run id> <results dir> <output pdf>
python3 plot_fig4.py 1 1 results/artifact_evaluation_results/ figure4.pdf
```

##### Table 4
The data from table 4 is generated by two different scripts. 
All full benchmarks should be complete before running these commands.

To generate a table of memory and storage utilization results:
```bash
cd evaluation
# usage: python3 get_mem_and_storage_use.py <num kvs> <kv1> <kv2> ... <num runs> <first run id> <results dir>
python3 get_mem_and_storage_use.py 4 redis pmemrocksdb viper capybarakv 1 1 results/artifact_evaluation_results/
```

To generate a table of startup times:
```bash
cd evaluation
# usage: python3 get_startup_times.py <results dir>
python3 get_startup_times.py results/artifact_evaluation_results/microbenchmark
```

### Claims and expected results

#### Claim 1: Verification
We claim that CapybaraKV verifies quickly using Verus. 
This claim is validated if CapybaraKV verifies successfully using the steps described in [Verification](#verification-5-minutes) above, and if verification times are reasonably similar to those presented in the paper or in the table in that section. Note that we expect to see a fair amount of variation between different machines; see the table in [Verifying CapybaraKV](#verifying-capybarakv) for some example data points.

One may also wish to audit the trusted components of CapybaraKV to check that we have proven a correct specification.
The claim that the specification is correct is validated if the auditor is satisfied that: 1) the specification correctly describes the expected behavior of CapybaraKV based on its description in the paper; 2) that our model of PM accurately represents the PM programming model and its expected crash behavior; and 3) the argument that PoWER corresponds to atomic invariants formalized in `pmem/power_sound_t.rs` is valid.


#### Claim 2: Line count and proof-to-code ratio
We claim that CapybaraKV has a low proof-to-code ratio of 2.6 and its line counts match those reported in the paper.

This claim is validated if the line counts and proof-to-code ratio outputted by `count_capybarakv_lines.py` match those in the paper. 

#### Claim 3: Performance
We claim that CapybaraKV achieves similar or better performance than several state-of-the art PM key-value stores.
We demonstrate this claim using two main experiments, a microbenchmark and a macrobenchmark.

This claim is validated if: 
- The plots generated by `plot_fig{2,3,4}.py` show similar performance/performance patterns to the versions of these plots in the paper.
- The output of `get_mem_and_storage_use.py` and `get_startup_times.py` is similar/shows similar performance patterns to the versions of these plots in the paper.

**NOTE**: Your results may differ from those in the paper if your evaluation environment uses any of the following:
- Emulated PM
- A PM device smaller than 128GiB
- Interleaved Optane PM

**Emulated PM**: Emulating PM using the steps described in [Emulated PM](#emulated-pm) presents a region of DRAM as if it is PM, but does *not* emulate the performance of Optane PM. 
DRAM has lower latency and higher bandwidth than Optane PM, so we expect to see non-trivial performance improvements across all experiments and systems.
**TODO**: more specific info about what we expect to be different

**<128GiB PM device**: The only data we expect to differ in a non-trivial way on smaller PM devices are start times for Viper and CapybaraKV.
The start times of these systems are heavily dependent on the size of the KV store since both have to initialize/reconstruct in-memory indexes.
We have only been able to collect data on 128GiB Optane PM and 64GiB emulated PM and do not have estimates for the expected start times on 64GiB Optane PM or 128GiB emulated PM.
We do expect that in all cases, the empty start time will be significantly less than the full start time of both systems (initializing empty indexes is faster than reconstructing full ones).
We also expect that CapybaraKV will take less time than Viper in both settings, as Viper memory-maps more individual files and indexes *hashes* of keys, which take additional time to compute.

**Interleaved Optane PM**: We do not expect significant performance differences running on interleaved Optane PM, although we have not tested our experiments in this environment. 
Viper has some performance optimizations for environments using interleaved NVDIMMs, but the number of DIMMS must be hardcoded and is set to 1 in the provided code, so we don't expect it to behave differently in this environment. 
It is possible that some or all systems may see improved throughput when running on interleaved DIMMs since accesses to different pages may be handled by different physical devices.

### Notes and troubleshooting

#### Changing configurations

The experiments read parameters like the PM device and results directory from a set of config files.
We provide config files for the settings we used in our original experiments.
If you'd like to use non-default settings, please use the provided `update_configs.sh` script as follows to update all configuration files with your preferred paths:
```bash
cd evaluation
./update_configs.sh <results dir relative to current location> <pm device>
```
You may optionally specify a new number of iterations for the macrobenchmarks as a third command line argument.
To reset to the defaults, run:
```bash
./update_configs results/artifact-evaluation /dev/pmem0 1
```

To update the number of keys used in the microbenchmarks, please modify the `experiment_keys` value directly in `microbenchmark_config_{64,128}GB.toml`. 

#### Emulated PM

CapybaraKV can also be run on DRAM by emulating PM. 
Note that performance results will differ significantly between DRAM and PM.
We describe the expected discrepancies in [Performance differences from Optane PM](#performance-differences-from-optane-pm).

##### Requirements

We recommend using a machine with at least **128GiB of DRAM**.

The YCSB experiments and most microbenchmarks need at least **64GiB of emulated PM**.

**Note:** DRAM that is used for emulated PM is not available as main memory, so do not use all DRAM to emulate PM; we have seen strange issues arise when running YCSB experiments, particularly with pmem-Redis, when too much DRAM is used to emulate PM.

##### Setting up emulated PM

1. Open `/etc/default/grub` using your text editor of choice (you may need to use `sudo`).
2. Find the line `GRUB_CMDLINE_LINUX=""` and modify it to `GRUB_CMDLINE_LINUX="memmap=YG!XG"` where `Y` is the number of GiB of emulated PM and `X` is the offset in DRAM to start the emulated PM region at. 
   - We suggest using an `X` of at least 4. 
   - Be sure that `X+Y`GiB does not exceed the total amount of DRAM.
3. Save the file and run `sudo update-grub`. 
4. Reboot.
5. After rebooting, you can check that PM has been emulated using one of the following commands:
   - `lsblk | grep pmem` should output a line like `pmem0  259:0    0    64G  0 disk`.
   - `ls /dev/ | grep pmem` should output `pmem0`. 

If neither command returns anything, check `/etc/default/grub` and make sure that 1) the value used for `X` is at least 4, 2) `X+Y`GiB does not exceed the total memory in the system, 3) `memmap` is spelled correctly. 
If you need to make changes, run `sudo update-grub` and reboot again.

You can now use the emulated PM as if it were Optane; the only difference will be in performance results.

#### Optane PM

If you use the provided PM machine or emulated PM, the PM will be set up properly for these experiments by default.
If you're using your own PM, you may need to change its configurations using `ipmctl` to replicate our experimental setup.

Our experiments expect **1 non-interleaved 128GiB NVDIMM in `fsdax` mode**.
The PM is most likely in `fsdax` by default. 
The mode of each namespace is listed when running `ndctl list --namespaces`. 
See the [NDCTL User Guide](https://docs.pmem.io/ndctl-user-guide/managing-namespaces) for instructions on changing the mode of a namespace.

If you need to change from an interleaved to a non-interleaved setup, use the following instructions. Note that **this will delete any existing data on the PM.**
1. Install dependencies: `sudo apt install ipmctl ndctl`.
   - `ipmctl` is not available from `apt` on newer distributions (e.g. Debian Trixie). We recommend using a slightly older distribution version (e.g. Debian Bookworm), if possible.
2. Delete all existing namespaces by calling `sudo ndctl destroy-namespace namespace0.0 --force` for each namespace, replacing 0.0 with the namespace number.
   - Namespaces can be listed using `ndctl list --namespaces`
3. Run `sudo ipmctl create -goal PersistentMemoryType=AppDirectNotInterleaved` and reboot the machine.
4. After rebooting, log back in and run `sudo ndctl enable-dimm all` to enable the NVDIMMs.
5. List NVDIMM regions using `ndctl list -Ri` and run `ndctl enable-region region<X>` for each one, where `<X>` is the region number.
6. Run `sudo ndctl create-namespace`, once for each namespace/NVDIMM. The same command needs to be run multiple times if there is more than one PM device.

To go from non-interleaved to interleaved, follow the same instructions, but run `sudo ipmctl create -goal PersistentMemoryType=AppDirect` in step 3.

For more information, see:
1. https://cdrdv2-public.intel.com/682059/CheatSheetv2.pdf
2. https://docs.pmem.io/ipmctl-user-guide/basic-usage


#### Troubleshooting 

**If you cannot see typed input in the terminal after running micro/macrobenchmarks**: Type `reset` (you won't be able to see it) and hit `Enter`. Pmem-Redis can sometimes mess up a terminal session and make new input invisible, but commands can still be run.

**If a `cargo run` command fails because `-lviper_wrapper` cannot be found**: Run `cargo clean` and try again.