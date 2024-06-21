# Experiments

## YCSB

### Setup
1. Install dependencies: `sudo apt install default-jdk default-jre maven`
2. Build the YCSB FFI layer: `cd ycsb_ffi; cargo build`.
3. Run `export LD_LIBRARY_PATH=~/verified-storage/ycsb_ffi/target/debug`


### redis setup
1. Clone `git@github.com:redis/redis.git`
2. Install dependencies: `sudo apt install tcl`
3. `cd redis` and run `make`

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