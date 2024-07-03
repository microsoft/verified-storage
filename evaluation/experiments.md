# Experiments

## YCSB

### Setup
1. Install dependencies: `sudo apt install default-jdk default-jre maven`
2. Build the YCSB FFI layer: `cd ycsb_ffi; cargo build`.
3. Build YCSB:
    - CapybaraKV: `mvn -pl site.ycsb:capybarakv-binding -am clean package`
    - redis (PM and standard): `mvn -pl site.ycsb:redis-binding -am clean package`
    - RocksDB: `mvn -pl site.ycsb:rocksdb-binding -am clean package`

3. Run `export LD_LIBRARY_PATH=~/verified-storage/ycsb_ffi/target/debug`

### redis setup
1. Clone `git@github.com:redis/redis.git`
2. Install dependencies: `sudo apt install tcl`
3. `cd redis` and run `make`

### RockSDB setup
RocksDB requires no additional setup; everything is handled by the YCSB RocksDB client.

### Running experiments
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
The `run_ycsb.sh` script runs all YCSB workloads that are supported by our KV store (i.e., all that don't include `scan` operations) with the options described above on a given KV store. Note that you still need to manually start a redis server before running this script on redis. The script expects the exact setup described in the Running Experiments section.