#!/bin/bash

export LD_LIBRARY_PATH=$PWD/ycsb_ffi/target/release:$PWD/viper_wrapper:$PWD/viper_deps/benchmark/build/src:$PWD/viper_deps/benchmark/include:$PWD/viper/benchmark

numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config config/mini_experiment_config.toml --capybarakv_config configs/mini_capybarakv_config.toml --workloads A
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db pmemrocksdb --experiment_config config/mini_experiment_config.toml --workloads A
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db redis --experiment_config config/mini_experiment_config.toml --workloads A
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db viper --experiment_config config/mini_experiment_config.toml --workloads A