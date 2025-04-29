#!/bin/bash

export LD_LIBRARY_PATH=$PWD/ycsb_ffi/target/release:$PWD/viper_wrapper:$PWD/viper_deps/benchmark/build/src:$PWD/viper_deps/benchmark/include:$PWD/viper/benchmark:/usr/local/lib

# 1 thread
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/mini_experiment_config1.toml --capybarakv_config configs/mini_capybarakv_config.toml --workloads A,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db pmemrocksdb --experiment_config configs/mini_experiment_config1.toml --workloads A,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db redis --experiment_config configs/mini_experiment_config1.toml --workloads A,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db viper --experiment_config configs/mini_experiment_config1.toml --workloads A,X

# 16 threads
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/mini_experiment_config16.toml --capybarakv_config configs/mini_capybarakv_config.toml --workloads A,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db pmemrocksdb --experiment_config configs/mini_experiment_config16.toml --workloads A,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db redis --experiment_config configs/mini_experiment_config16.toml --workloads A,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db viper --experiment_config configs/mini_experiment_config16.toml --workloads A,X