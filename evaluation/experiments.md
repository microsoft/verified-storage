# Experiments

## YCSB
### Setup
1. Install dependencies: `sudo apt install default-jdk default-jre maven libpmemobj-dev libsnappy-dev pkg-config autoconf automake libtool libndctl-dev libdaxctl-dev libnuma-dev daxctl libzstd-dev cmake build-essential`
2. Build the YCSB FFI layer: `cd ycsb_ffi; cargo build --release`.
3. Build YCSB:
    - CapybaraKV: `cd YCSB; mvn -pl site.ycsb:capybarakv-binding -am clean package`
    - redis (PM and standard): `cd YCSB; mvn -pl site.ycsb:redis-binding -am clean package`
    - pmem-RocksDB: `cd YCSB; mvn -pl site.ycsb:pmemrocksdb-binding -am clean package`

3. Run `export LD_LIBRARY_PATH=~/verified-storage/evaluation/ycsb_ffi/target/release`
4. Run `export JAVA_HOME=/usr/lib/jvm/java-X-openjdk-amd64/` where `X` is the Java version to use.

### redis setup
<!-- 1. Install gcc-8 by running `sudo apt install gcc-8`. This may fail on newer Ubuntu distributions; if it does, run:
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
Make sure `gcc-8` is selected.-->
1. `cd` to `pmem-redis` and run `make USE_NVM=yes` 

If redis doesn't build, the following may help:
1. Install gcc-8 by running `sudo apt install gcc-8`. This may fail on newer Ubuntu distributions; if it does, run:
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
2. Check that the following files and directories are present. They should be, but an bad .gitignore or clean can sometimes cause issues. If any are missing, create them and copy them in from the repository manually.
    - Check that `pmem-redis/deps/jemalloc/bin/` exists and that it contains the following files: `jemalloc-config.in`, `jemalloc.sh.in`, and `jeprof.in`. If the directory does not exist, or if any of these files are missing or empty, 
    - Check that `pmem-redis/deps/pmdk/src/jemalloc/bin` exists and that it contains `jemalloc.sh.in` and `pprof`.
    - Check that `pmem-redis/deps/memkind/jemalloc/bin` exists and that it contains `jemalloc-config.in`, `jemalloc.sh.in`, and `jeprof.in`.


#### pmem-rocksdb
1. `cd` to `pmem-rocksdb` and build with `make rocksdbjava ROCKSDB_ON_DCPMM=1 DISABLE_WARNING_AS_ERROR=true -j 8`

## Running experiments

To run all YCSB experiments on a DB, cd to `evaluation/` and run:
```
./run_ycsb.sh <db name> <results dir> use_pm
```
Omit the `use_pm` argument to run the experiments in a regular file. If using emulated PM, include the `use_pm` argument.


### Individual experiments

These instructions assume that a PM device is/can be mounted at `/mnt/pmem/`.

#### CapybaraKV
1. To initialize the KV before running any workloads, `cd` to `ycsb_ffi/src` and run `cargo_run`. This should be repeated before each `load` workload.
2. `cd` to `YCSB` and run ``./bin/ycsb load capybarakv -s -P workloads/workloada`

TODO: other systems

<!-- #### RocksDB
1. Create a directory `~/rocksdb_files` to store the database's files.
2. Run `./bin/ycsb load pmemrocksdb -s -P workloads/workloada -p rocksdb.dir=~/rocksdb_files -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true`

*Note:* if running experiments individually, the KV store must be initialized prior to `load` workloads by running `cargo run` in the `ycsb_ffi` crate.

#### redis
1. Create `~/redis_files` to store the database's files.
2. Start redis with `cd pmem-redis/src; ./redis-server --dir ~/redis_files` and take note of the port, usually 6379 (or specify one to use by adding `--port <port>` to the `redis-server` command).
2. In a different terminal, `cd YCSB` and run `./bin/ycsb load redis -s -P workloads/workloada -p "redis.host=localhost" -p "redis.port=<port>"`  -->

<!-- ### Running experiments
In `YCSB/`:
1. `./bin/ycsb load capybarakv -s -P workloads/workloada`
2. RocksDB: 
    1. Create a directory `~/rocksdb_files` to store the database's files.
    2. Run `./bin/ycsb load rocksdb -s -P workloads/workloada -p rocksdb.dir=~/rocksdb_files -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true`
        - I think allowing `mmap` reads and writes will make the DBs behave more similarly to each other
3. redis: 
    1. Create `~/redis_files` to store the database's files.
    2. Start redis with `cd redis/src; ./redis-server --dir ~/redis_files` and take note of the port, usually 6379 (or specify one to use by adding `--port <port>` to the `redis-server` command).
    2. In a different terminal, `cd YCSB` and run `./bin/ycsb load redis -s -P workloads/workloada -p "redis.host=localhost" -p "redis.port=<port>"` 

### YCSB script
The `run_ycsb.sh` script runs all YCSB workloads that are supported by our KV store (i.e., all that don't include `scan` operations) with the options described above on a given KV store. Note that you still need to manually start a redis server before running this script on redis. The script expects the exact setup described in the Running Experiments section. -->