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
BG=${BOLD}${GREEN}

# 1. Install Rust and automatically select default installation
printf "${BOLD}${MAGENTA}Installing Rust...${NC}\n"
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
printf "${BOLD}${MAGENTA}Done installing Rust!${NC}\n\n\n"

# 2. Confirm that verified-storage crates build successfully
printf "${BOLD}${MAGENTA}Building verified-storage crates...${NC}\n"
cd $VERIF_STORAGE_DIR/deps_hack; cargo build --release
cd $VERIF_STORAGE_DIR/pmsafe; cargo build --release
cd $VERIF_STORAGE_DIR/storage_node/src; cargo build --release
printf "${BOLD}${MAGENTA}Done building verified-storage crates!${NC}\n\n\n"

# 3. Clone and build Verus
printf "${BOLD}${MAGENTA}Cloning and building Verus...${NC}\n"
cd $VERIF_STORAGE_DIR
if [ -d verus ]; 
then 
    printf "${BOLD}${MAGENTA}Verus is already cloned. Rebuilding it...${NC}\n"
else 
    git clone https://github.com/verus-lang/verus.git;
fi
cd $VERUS_DIR; source ../tools/activate; ./tools/get-z3.sh; vargo build --release
printf "${BOLD}${MAGENTA}Done building Verus!${NC}\n\n\n"

# 4. Confirm that CapybaraKV verifies
printf "${BOLD}${MAGENTA}Verifying CapybaraKV...${NC}\n"
cd $VERIF_STORAGE_DIR/storage_node/src/; ./verify.sh
printf "${BOLD}${MAGENTA}Done verifying CapybaraKV!${NC}\n\n\n"

# 5. Install other apt dependencies
sudo apt install default-jdk default-jre maven libpmemobj-dev libsnappy-dev \
    pkg-config autoconf automake libtool libndctl-dev libdaxctl-dev libnuma-dev \
    daxctl libzstd-dev cmake build-essential liblz4-dev libpmempool-dev valgrind \
    python3-toml numactl

# 6. Download Maven for YCSB
cd $PROJECT_DIR
wget https://dlcdn.apache.org/maven/maven-3/3.9.9/binaries/apache-maven-3.9.9-bin.tar.gz
tar -xvf apache-maven-3.9.9-bin.tar.gz