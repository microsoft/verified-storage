#!/bin/bash

export LD_LIBRARY_PATH=$PWD/ycsb_ffi/target/release:$PWD/viper_wrapper:$PWD/viper_deps/benchmark/build/src:$PWD/viper_deps/benchmark/include:$PWD/viper/benchmark

# viper needs to be run separately to determine how much storage it uses for Load A because we don't
# let it resize in the normal YCSB experiments to keep things fair
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db viper --experiment_config configs/experiment_config_mem_storage.toml --workloads A
# the capybarakv storage measurement experiment uses slightly less space than the regular-case experiments
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/experiment_config_mem_storage.toml --capybarakv_config configs/capybarakv_config_mem_storage.toml --workloads A

numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/experiment_config1.toml 
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db pmemrocksdb --experiment_config configs/experiment_config1.toml --workloads A,B,C,D,F,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db redis --experiment_config configs/experiment_config1.toml --workloads A,B,C,D,F,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db viper --experiment_config configs/experiment_config1.toml --workloads A,B,C,D,F,X

numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/experiment_config16.toml 
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db pmemrocksdb --experiment_config configs/experiment_config16.toml --workloads A,B,C,D,F,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db redis --experiment_config configs/experiment_config16.toml --workloads A,B,C,D,F,X
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db viper --experiment_config configs/experiment_config16.toml --workloads A,B,C,D,F,X

numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/experiment_config8.toml
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/experiment_config4.toml
numactl --membind 0 --cpunodebind 0 python3 run_ycsb.py --db capybarakv --experiment_config configs/experiment_config2.toml
