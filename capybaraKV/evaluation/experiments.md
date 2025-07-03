# Experiments

**NOTE**: these are mostly superseded by the artifact READMEs and the `setup.sh` script. Artifact evaluators can ignore this file.

## YCSB

Tested Linux environments:
- Linux v6.7 and 6.12
- Debian Trixie

### Setup
1. Install dependencies: `sudo apt install default-jdk default-jre maven libpmemobj-dev libsnappy-dev pkg-config autoconf automake libtool libndctl-dev libdaxctl-dev libnuma-dev daxctl libzstd-dev cmake build-essential liblz4-dev libpmempool-dev valgrind; pip3 install toml`
2. Install Maven:
    - Download and untar a binary from https://maven.apache.org/download.cgi
    - Add the `bin` folder in the extracted directory to your `PATH`.

3. Set up Viper
    - Clone from GitHub: `git clone git@github.com:hpides/viper.git` into a sibling directory of `evaluation/benchmark`
    - Viper has two main dependencies, `concurrentqueue` and `benchmark`, which are already in `evaluation/viper_deps`. 
    - Follow these instructions to build the benchmark dependency and install it globally:
    ```
    # Go to the library root directory
    $ cd viper_deps/benchmark
    # Make a build directory to place the build output.
    $ cmake -E make_directory "build"
    # Generate build system files with cmake, and download any dependencies.
    $ cmake -DBENCHMARK_DOWNLOAD_DEPENDENCIES=on -DCMAKE_BUILD_TYPE=Release -S . -B "build" -DBUILD_SHARED_LIBS=ON
    # Build the library.
    $ cmake --build "build" --config Release
    $ sudo cmake --build "build" --config Release --target install
    ```
    - Follow these instructions to build the `libpmemobj++` dependency:
    ```
    cd viper_deps/libpmemobj-cpp
    mkdir build
    cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=./build
    make
    make install
    ```
    - Build required Viper wrapper libraries:
    ```
    cd viper_wrapper
    make all
    ```
    
**To compile Viper wrapper on its own:** `clang++ viper_wrapper.cpp -I../viper/include -I../viper_deps/concurrentqueue -I../viper/benchmark -I../viper_deps/benchmark/include -std=c++17 -lpmem -lpmemobj -lpmempool -I../viper_deps/libpmemobj-cpp/include -mclwb -DVIPER_BUILD_BENCHMARKS=ON -lbenchmark -DCXX_COMPILATION`

2. Build the YCSB FFI layer: `cd ycsb_ffi; cargo build --release`.
3. Run `export LD_LIBRARY_PATH=$HOME/verified-storage/evaluation/ycsb_ffi/target/release:$HOME/verified_storage/evaluation/viper_wrapper:$HOME/verified-storage/evaluation/viper_deps/benchmark/build/src:$HOME/verified-storage/evaluation/viper_deps/benchmark/include:$HOME/verified_storage/evaluation/viper/benchmark`

<!-- TODO: for some reason that path doesn't work but this one does: 
```
export LD_LIBRARY_PATH=/mnt/local_ssd/home/hayley/verified-storage/evaluation/viper_deps/benchmark/include:/mnt/local_ssd/home/hayley/verified-storage/evaluation/viper_deps/benchmark/include:/mnt/local_ssd/home/hayley/verified-storage/evaluation/viper_wrapper:/mnt/local_ssd/home/hayley/verified_storage/evaluation/viper/benchmark:/mnt/local_ssd/home/hayley/verified-storage/evaluation/ycsb_ffi/target/release:/mnt/local_ssd/home/hayley/verified_storage/evaluation/viper_wrapper:/mnt/local_ssd/home/hayley/verified-storage/evaluation/viper_deps/benchmark/build/src
```
what's the difference? we were missing a couple of benchmark ones, but that wouldn't really make sense...it's the absolute paths -->


4. Run `export JAVA_HOME=/usr/lib/jvm/java-X-openjdk-amd64/` where `X` is the Java version to use.
5. Build pmem-RocksDB: `cd` to `pmem-rocksdb` and build with `make rocksdbjava ROCKSDB_ON_DCPMM=1 DISABLE_WARNING_AS_ERROR=true -j 8`
6. Build redis: `cd` to `pmem-redis` and run `make USE_NVM=yes` 
7. Build YCSB:
    - CapybaraKV: `cd YCSB; mvn -pl site.ycsb:capybarakv-binding -am clean package`
    - redis (pmem and standard): `cd YCSB; mvn -pl site.ycsb:redis-binding -am clean package`
    - pmem-RocksDB: `cd YCSB; mvn -pl site.ycsb:pmemrocksdb-binding -am clean package`
    
8. Build the benchmark crate: `cargo +nightly build --release`
    - As of 03/11/2025, the `+nightly` arg is required for verified storage to build properly

### redis troubleshooting
If redis doesn't build, the following may help:
1. Check that the following files and directories are present. They should be, but an bad .gitignore or clean can sometimes cause issues. If any are missing, create them and copy them in from the repository manually.
    - Check that `pmem-redis/deps/jemalloc/bin/` exists and that it contains the following files: `jemalloc-config.in`, `jemalloc.sh.in`, and `jeprof.in`. If the directory does not exist, or if any of these files are missing or empty, 
    - Check that `pmem-redis/deps/pmdk/src/jemalloc/bin` exists and that it contains `jemalloc.sh.in` and `pprof`.
    - Check that `pmem-redis/deps/memkind/jemalloc/bin` exists and that it contains `jemalloc-config.in`, `jemalloc.sh.in`, and `jeprof.in`.
2. Install gcc-8 by running `sudo apt install gcc-8`. This may fail on newer Ubuntu distributions; if it does, run:
    ```
    sudo cat <<EOF | sudo tee /etc/apt/sources.list.d/gcc-8.list
    deb http://old-releases.ubuntu.com/ubuntu/ impish main restricted universe multiverse
    EOF
    ```
    Then
    ```
    sudo apt update
    sudo apt install gcc-8
    sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 25
    sudo update-alternatives --config gcc
    ```
    Make sure `gcc-8` is selected.

### pmem-rocksdb troubleshooting
If pmem-rocksdb builds but the YCSB bindings give an error that looks something like "class file has wrong version 65.0, should be 61.0", make sure `JAVA_HOME` points to the most recent installed Java version.

## Running experiments

To run all YCSB experiments on a given DB:
1. Set the desired configurations in `experiment_config.toml` and `capybarakv_config.toml`. The value of `num_keys` in `capybarakv_config.toml` should be **greater than** the the value of `record_count` in `experiment_config.toml`, as several YCSB experiments insert additional records, updates in CapybaraKV require there to be at least one free value table entry, and multi-threaded experiments on CapybaraKV will not perfectly evenly distribute keys across shards.
    - `experiment_config.toml` sets experiment-related options like the number of threads, the PM device and mount point, and the number of iterations to run.
    - `capybarakv_config.toml` specifies CapybaraKV-specific options such as the name and size of backing file and the number of keys to allocate space for. 
2. `cd` to `evaluation/` and run:
```
python3 run_ycsb.py --db <db name> --experiment_config <path to experiment config file>
```

### Troubleshooting

Check the files in the result directory to get error information if an experiment fails. Some common issues are listed below.

- If you get `OutOfSpace` errors with CapybaraKV when updating records, make sure the number of keys allocated in the database (specified by `num_keys` in the CapybaraKV configuration file) is larger than the `record_count` value specified in the experiment configuration file. CapybaraKV uses copy-on-write to update records and thus requires some additional free slots for these operations to succeed. 

### Individual experiments

These instructions assume that a PM device is already mounted with ext4-DAX at `/mnt/pmem/`. 
They all specify how to run the `LoadA` workload; to run others, replace `load` with `run` to run a `RunX` workload and change the `workloads/workloadx` path to reflect the desired workload.
**Note**: Running RunA, RunB, RunC, RunD must be preceded by running LoadA; RunF must be preceded by running LoadE.
**Note**: RunE is currently not supported by CapybaraKV.

#### CapybaraKV
1. To initialize the KV before running any workloads, `cd` to `ycsb_ffi/src` and run `cargo_run`. This should be repeated before each `load` workload.
2. `cd` to `YCSB` and run 
```
./bin/ycsb load capybarakv -s -P workloads/workloada -p capybarakv_config=../capybarakv_config.toml
```

#### pmem-RocksDB
1. `cd` to YCSB and run:
```
./bin/ycsb load pmemrocksdb -s -P workloads/workloada -p rocksdb.dir=/mnt/pmem/ -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true
```

#### pmem-redis
1. `cd` to `pmem-redis/` and run 
```
./src/redis-server redis.conf &
```
This starts the redis server running in the background, using `/mnt/pmem/` to store data. The `redis.conf` file is preconfigured for use in these experiments.
2. `cd` to YCSB and run:
```
./bin/ycsb load redis -s -P workloads/workloada -p redis.host=127.0.0.1 -p redis.port=6379
```

## Latency experiments

To run latency and setup microbenchmarks, `cd` to `evaluation/benchmark` and run `cargo run --release -- <output dir path>`.

To obtain the average startup time across all iterations in `empty_setup` or `full_setup`, `cd` to the target directory (e.g. `<output dir path>/capybarakv/empty_setup`) and run `awk '{sum+=$1} END {print sum/NR}' *`

# Windows

**Note**: Currently, only CapybaraKV is supported on Windows for running YCSB workloads. Other databases like Redis and pmem-RocksDB may not function correctly or may require additional setup that is not covered in this guide.

## Setup
1. Install Lastest JDK via https://jdk.java.net/
2. Install Maven via https://maven.apache.org/install.html
3. Set environment variables in PowerShell

```powershell
$env:JAVA_HOME="C:\Users\$Env:UserName\jdk-22" # Replace with your JDK path
$env:PATH="$env:PATH;C:\Users\$Env:UserName\apache-maven-3.9.9\bin"
```

4. Build YCSB FFI layer

```powershell
cd evaluation\ycsb_ffi
cargo build --release
$env:PATH="$env:PATH;C:\Users\$Env:UserName\verified-storage\evaluation\ycsb_ffi\target\release"
```

5. Run ycsb_ffi under `evaluation/` to prepare the database

```powershell
.\ycsb_ffi\target\release\ycsb_ffi.exe .\capybarakv_config_win.toml .\experiment_config_win.toml
```

6. Build YCSB CapybaraKV binding

```powershell
cd YCSB; mvn -pl site.ycsb:capybarakv-binding -am clean package
```

7. Run YCSB workload under `evaluation/`

```powershell
pip3 install toml
python run_ycsb.py --db capybarakv
```

