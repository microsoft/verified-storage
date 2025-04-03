#!/bin/bash

# exit on error
set -e 
set -o pipefail

PROJECT_DIR=$(pwd)/../..
VERIF_STORAGE_DIR=$PROJECT_DIR/verified-storage
VERUS_DIR=$PROJECT_DIR/verus

RED="\e[32m"
GREEN="\e[32m"
MAGENTA="\e[35m"
BOLD=$(tput bold)
NC="\e[0m"

LD_LIBRARY_PATH=$VERIF_STORAGE_DIR/evaluation/ycsb_ffi/target/release:$VERIF_STORAGE_DIR/evaluation/viper_wrapper:$VERIF_STORAGE_DIR/evaluation/viper_deps/benchmark/build/src:$VERIF_STORAGE_DIR/evaluation/viper_deps/benchmark/include:$VERIF_STORAGE_DIR/evaluation/viper/benchmark
JAVA_HOME=/usr/lib/jvm/java-21-openjdk-amd64/

# 1. Install apt dependencies
# TODO: is valgrind necessary?
printf "${BOLD}${MAGENTA}Installing dependencies...${NC}\n"
sudo apt -y install default-jdk default-jre libpmemobj-dev libsnappy-dev \
    pkg-config autoconf automake libtool libndctl-dev libdaxctl-dev libnuma-dev \
    daxctl libzstd-dev cmake build-essential liblz4-dev libpmempool-dev valgrind \
    python3-toml numactl llvm-dev libclang-dev clang libpmem1 libpmem-dev \
    python3-pip unzip
printf "${BOLD}${MAGENTA}Done installing dependencies!${NC}\n\n\n"

# 2. Install Rust and automatically select default installation
printf "${BOLD}${MAGENTA}Installing Rust...${NC}\n"
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
printf "${BOLD}${MAGENTA}Done installing Rust!${NC}\n\n\n"

# 3. Confirm that verified-storage crates build successfully
printf "${BOLD}${MAGENTA}Building verified-storage crates...${NC}\n"
cd $VERIF_STORAGE_DIR/deps_hack; cargo build --release
cd $VERIF_STORAGE_DIR/pmsafe; cargo build --release
cd $VERIF_STORAGE_DIR/storage_node/src; cargo build --release
printf "${BOLD}${MAGENTA}Done building verified-storage crates!${NC}\n\n\n"

# 4. Clone and build Verus
printf "${BOLD}${MAGENTA}Cloning and building Verus...${NC}\n"
cd $PROJECT_DIR
if [ -d verus ]; 
then 
    printf "${BOLD}${MAGENTA}Verus is already cloned. Rebuilding it...${NC}\n"
else 
    git clone https://github.com/verus-lang/verus.git;
fi
cd $VERUS_DIR/source; ./tools/get-z3.sh; /bin/bash -c "source ../tools/activate; vargo build --release"
printf "${BOLD}${MAGENTA}Done building Verus!${NC}\n\n\n"

# 5. Confirm that CapybaraKV verifies
printf "${BOLD}${MAGENTA}Verifying CapybaraKV...${NC}\n"
cd $VERIF_STORAGE_DIR/storage_node/src/; ./verify.sh
printf "${BOLD}${MAGENTA}Done verifying CapybaraKV!${NC}\n\n\n"

# 6. Download Maven for YCSB
printf "${BOLD}${MAGENTA}Downloading Maven...${NC}\n"
cd $PROJECT_DIR
if [ -d maven ];
then
    printf "${BOLD}${MAGENTA}Maven already exists here, skipping...${NC}\n"
else
    wget https://dlcdn.apache.org/maven/maven-3/3.9.9/binaries/apache-maven-3.9.9-bin.tar.gz
    tar -xvf apache-maven-3.9.9-bin.tar.gz
    mv apache-maven-3.9.9 maven
fi
PATH=$PATH:$PROJECT_DIR/maven/bin
printf "${BOLD}${MAGENTA}Done downloading Maven${NC}\n\n\n"

#7. Build YCSB FFI layer
printf "${BOLD}${MAGENTA}Building YCSB FFI layer for CapybaraKV...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/ycsb_ffi
cargo build --release
printf "${BOLD}${MAGENTA}Done building YCSB FFI layer for CapybaraKV!${NC}\n\n\n"

# 8. Building pmem-RocksDB
printf "${BOLD}${MAGENTA}Building pmem-RocksDB...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/pmem-rocksdb
make rocksdbjava ROCKSDB_ON_DCPMM=1 DISABLE_WARNING_AS_ERROR=true -j
printf "${BOLD}${MAGENTA}Done building pmem-RocksDB!${NC}\n\n\n"

# 9. Building pmem-Redis
printf "${BOLD}${MAGENTA}Building pmem-redis...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/pmem-redis
make USE_NVM=yes
printf "${BOLD}${MAGENTA}Done building pmem-redis!${NC}\n\n\n"

# 10. Build YCSB bindings
printf "${BOLD}${MAGENTA}Building YCSB bindings...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/YCSB
mvn -pl site.ycsb:capybarakv-binding -am clean package
mvn -pl site.ycsb:redis-binding -am clean package 
mvn -pl site.ycsb:pmemrocksdb-binding -am clean package
mvn -pl site.ycsb:viper-binding -am clean package
printf "${BOLD}${MAGENTA}Done building YCSB bindings!${NC}\n\n\n"

#11. Build Viper dependencies
printf "${BOLD}${MAGENTA}Building Viper dependencies...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/viper_deps/libpmemobj-cpp
mkdir build
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=./build
make
make install
printf "${BOLD}${MAGENTA}Done building Viper dependencies!${NC}\n\n\n"

# 12. Build Viper wrapper
printf "${BOLD}${MAGENTA}Building Viper wrapper...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/viper_wrapper
make all JAVA_HOME=$JAVA_HOME
printf "${BOLD}${MAGENTA}Done building Viper wrapper!${NC}\n\n\n"

# 13. Creating libpthread link in case it is not already there
# TODO: what if libpthread.so.0 isn't there either? Should look for the correct file and fill it in
if [ ! -f /usr/lib/x86_64-linux-gnu/libpthread.so ]; 
then 
    printf "${BOLD}${MAGENTA}Creating link to libpthread.so...${NC}\n"
    sudo ln -s /usr/lib/x86_64-linux-gnu/libpthread.so.0 /usr/lib/x86_64-linux-gnu/libpthread.so
    printf "${BOLD}${MAGENTA}Done creating link to libpthread.so!${NC}\n\n\n"
fi

printf "${BOLD}${MAGENTA}Done!${NC}"