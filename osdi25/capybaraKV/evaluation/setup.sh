#!/bin/bash

# exit on error
set -e
set -o pipefail

PROJECT_DIR=`realpath $(pwd)/../../../..`
VERIF_STORAGE_DIR=$PROJECT_DIR/verified-storage/osdi25/capybaraKV
VERUS_DIR=$PROJECT_DIR/verus

RED="\e[31m"
GREEN="\e[32m"
MAGENTA="\e[35m"
BOLD=$(tput bold)
NC="\e[0m"

total_steps=13
current_step=0

JAVA_HOME=""

VERUS_HASH=a71d271765344ed821f563895c69ff4775718a85

step() {
    printf "${MAGENTA}[${current_step}/${total_steps}]${NC} "
    current_step=$((current_step+1))
}

LD_LIBRARY_PATH=$VERIF_STORAGE_DIR/evaluation/ycsb_ffi/target/release:$VERIF_STORAGE_DIR/evaluation/viper_wrapper:$VERIF_STORAGE_DIR/evaluation/viper_deps/benchmark/build/src:$VERIF_STORAGE_DIR/evaluation/viper_deps/benchmark/include:$VERIF_STORAGE_DIR/evaluation/viper/benchmark:/usr/local/lib
ld_lib_path="export LD_LIBRARY_PATH=${LD_LIBRARY_PATH}"
grep -qxF "${ld_lib_path}" $HOME/.bashrc || echo $ld_lib_path >> $HOME/.bashrc

OS=""
VER=""
# some dependency installations depend on the distro
# noble needs gcc-14
if [ -f /etc/os-release ]; then
    # freedesktop.org and systemd
    . /etc/os-release
    OS=$NAME
    VER=$VERSION_ID
elif [ -f /etc/lsb-release ]; then
    # For some versions of Debian/Ubuntu without lsb_release command
    . /etc/lsb-release
    OS=$DISTRIB_ID
    VER=$DISTRIB_RELEASE
fi

echo "$OS"
echo "$VER"
echo "$VERSION_CODENAME"


if [[ $OS == "Debian"* ]]; then 
    if [[ $VERSION_CODENAME != "trixie" && $VERSION_CODENAME != "bookworm" ]]; then 
        printf "${RED}${BOLD}You are using an untested and potentially unsupported OS version ($OS $VERSION_CODENAME). This script may not work properly. Continue anyway? [y/n]: "
        read continue
        while [[ $continue != "y" ]]; do 
            if [[ $continue == "n" ]]; then 
                echo "Exiting"
                exit 
            else
                printf "Unrecognized input. Please entry y or n: "
            fi
        done 
        echo "Continuing"
    fi
elif [[ $OS == "Ubuntu" ]]; then 
    if [[ $VER != 22.04 && $VER != 24.04 ]]; then 
        printf "${RED}${BOLD}You are using an untested and potentially unsupported OS version ($OS $VERSION_CODENAME). This script may not work properly. Continue anyway? [y/n]: "
        read continue
        while [[ $continue != "y" ]]; do 
            if [[ $continue == "n" ]]; then 
                echo "Exiting"
                exit
            else
                printf "Unrecognized input. Please entry y or n: "
            fi
        done 
        echo "Continuing"
    fi 
else 
    printf "${RED}${BOLD}You are using an untested distribution ($OS). This script may not work properly. Continue anyway? [y/n]: "
    read continue
    while [[ $continue != "y" ]]; do 
        if [[ $continue == "n" ]]; then 
            echo "Exiting"
            exit
        else
            printf "Unrecognized input. Please entry y or n: "
        fi
    done 
    echo "Continuing"
fi

# 1. Install apt dependencies
# TODO: is valgrind necessary?
step; printf "${BOLD}${MAGENTA}Installing dependencies...${NC}\n"
sudo apt update
sudo apt -y install default-jdk default-jre libpmemobj-dev libsnappy-dev \
    pkg-config autoconf automake libtool libndctl-dev libdaxctl-dev libnuma-dev \
    daxctl libzstd-dev cmake build-essential liblz4-dev libpmempool-dev valgrind \
    python3-toml numactl llvm-dev libclang-dev clang libpmem1 libpmem-dev \
    python3-pip python3-prettytable python3-numpy python3-matplotlib unzip curl \
    wget gcc-12 g++-12
printf "${BOLD}${MAGENTA}Done installing dependencies!${NC}\n\n\n"

# 2. Find java installation and set JAVA_HOME
step; printf "${BOLD}${MAGENTA}Finding JAVA_HOME...${NC}\n"
if [ -z $JAVA_HOME ]; then
    if type -p java; then
        echo found java executable in PATH
        _java=java
    elif [[ -n "$JAVA_HOME" ]] && [[ -x "$JAVA_HOME/bin/java" ]];  then
        echo found java executable in JAVA_HOME     
        _java="$JAVA_HOME/bin/java"
    else
        printf "${BOLD}${RED}Unable to find Java. Please check that it has been successfully installed.${NC}\n"
        exit
    fi

    if [[ "$_java" ]]; then
        version=$("$_java" -version 2>&1 | awk -F '"' '/version/ {print $2}')
        major_version=$(echo $version | awk -F '.' '{print $1}')
        JAVA_HOME="/usr/lib/jvm/java-${major_version}-openjdk-amd64/"
    fi

    if [ -n $JAVA_HOME ]; then 
        # check that the directory we set JAVA_HOME to actually exists
        if [ ! -d $JAVA_HOME ]; then 
            printf "${BOLD}${RED}Automatically-obtained JAVA_HOME ${JAVA_HOME} does not exist. Please manually set JAVA_HOME in the setup.sh script.${NC}\n"
            exit
        else 
            printf "${MAGENTA}JAVA_HOME is set to ${JAVA_HOME}${NC}\n"
        fi 
    else 
        printf "${BOLD}${RED}Unable to set JAVA_HOME. Please confirm that Java has been successfully installed.${NC}\n"
        exit
    fi
else 
    printf "${MAGENTA}JAVA_HOME is already set to ${JAVA_HOME}${NC}\n"
fi
set_java_home="export JAVA_HOME=${JAVA_HOME}"
grep -qxF "${set_java_home}" $HOME/.bashrc || echo $set_java_home >> $HOME/.bashrc
printf "${BOLD}${MAGENTA}Done finding Java!${NC}\n\n\n"


# 3. Install Rust and automatically select default installation
step; printf "${BOLD}${MAGENTA}Installing Rust...${NC}\n"
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
printf "${BOLD}${MAGENTA}Done installing Rust!${NC}\n\n\n"

# 4. Install tokei for line counting
step; printf "${BOLD}${MAGENTA}Installing cargo dependencies...${NC}\n"
cargo install tokei
printf "${BOLD}${MAGENTA}Done installing cargo dependencies!${NC}\n\n\n"

# 5. Confirm that verified-storage crates build successfully
step; printf "${BOLD}${MAGENTA}Building verified-storage crates...${NC}\n"
cd $VERIF_STORAGE_DIR/deps_hack; cargo build --release
cd $VERIF_STORAGE_DIR/pmcopy; cargo build --release
cd $VERIF_STORAGE_DIR/storage_node/src; cargo build --release
printf "${BOLD}${MAGENTA}Done building verified-storage crates!${NC}\n\n\n"

# 6. Clone and build Verus
step; printf "${BOLD}${MAGENTA}Cloning Verus and dependencies...${NC}\n"
cd $PROJECT_DIR
if [ -d verus ]; 
then 
    printf "${MAGENTA}Verus is already present.${NC}\n"
    cd $VERUS_DIR/source
else 
    printf "${MAGENTA}Verus is not present, cloning...${NC}\n"
    git clone https://github.com/verus-lang/verus.git;
    cd $VERUS_DIR/source
    git checkout $VERUS_HASH
fi

if [ ! -f z3 ];
then
    printf "${MAGENTA}Z3 is not present, downloading...${NC}\n"
    ./tools/get-z3.sh
else 
    printf "${MAGENTA}Z3 is already present.${NC}\n"
fi
printf "${BOLD}${MAGENTA}Done cloning Verus and dependencies!${NC}\n\n\n"

step; printf "${BOLD}${MAGENTA}Building Verus...${NC}\n"
/bin/bash -c "source ../tools/activate; vargo build --release"
printf "${BOLD}${MAGENTA}Done building Verus!${NC}\n\n\n"

path_verus="export PATH=\$PATH:${VERUS_DIR}/source/target-verus/release"
grep -qxF "${path_verus}" $HOME/.bashrc || echo $path_verus >> $HOME/.bashrc

# # 7. Confirm that CapybaraKV verifies
# printf "${BOLD}${MAGENTA}Verifying CapybaraKV...${NC}\n"
# cd $VERIF_STORAGE_DIR/storage_node/src/; ./verify.sh
# printf "${BOLD}${MAGENTA}Done verifying CapybaraKV!${NC}\n\n\n"

# 8. Download Maven for YCSB
step; printf "${BOLD}${MAGENTA}Downloading Maven...${NC}\n"
cd $PROJECT_DIR
if [ -d maven ];
then
    printf "${BOLD}${MAGENTA}Maven already exists here, skipping...${NC}\n"
else
    wget https://dlcdn.apache.org/maven/maven-3/3.9.9/binaries/apache-maven-3.9.9-bin.tar.gz
    tar -xvf apache-maven-3.9.9-bin.tar.gz
    mv apache-maven-3.9.9 maven
    rm apache-maven-3.9.9-bin.tar.gz
fi
path_maven="export PATH=\$PATH:${PROJECT_DIR}/maven/bin"
grep -qxF "${path_maven}" $HOME/.bashrc || echo $path_maven >> $HOME/.bashrc
printf "${BOLD}${MAGENTA}Done downloading Maven${NC}\n\n\n"
export PATH=$PATH:${PROJECT_DIR}/maven/bin

# 9. Build YCSB FFI layer
step; printf "${BOLD}${MAGENTA}Building YCSB FFI layer for CapybaraKV...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/ycsb_ffi
cargo build --release
printf "${BOLD}${MAGENTA}Done building YCSB FFI layer for CapybaraKV!${NC}\n\n\n"

# 10. Building pmem-RocksDB
step; printf "${BOLD}${MAGENTA}Building pmem-RocksDB...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/pmem-rocksdb
make rocksdbjava ROCKSDB_ON_DCPMM=1 DISABLE_WARNING_AS_ERROR=true JAVA_HOME=$JAVA_HOME -j 16
printf "${BOLD}${MAGENTA}Done building pmem-RocksDB!${NC}\n\n\n"

# 11. Building pmem-Redis
step; printf "${BOLD}${MAGENTA}Building pmem-redis...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/pmem-redis
make USE_NVM=yes
printf "${BOLD}${MAGENTA}Done building pmem-redis!${NC}\n\n\n"

# 12. Build YCSB bindings
step; printf "${BOLD}${MAGENTA}Building YCSB bindings...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/YCSB
mvn -pl site.ycsb:capybarakv-binding -am clean package
mvn -pl site.ycsb:redis-binding -am clean package 
mvn -pl site.ycsb:pmemrocksdb-binding -am clean package
mvn -pl site.ycsb:viper-binding -am clean package
printf "${BOLD}${MAGENTA}Done building YCSB bindings!${NC}\n\n\n"

# 13. Build Viper dependencies
step; printf "${BOLD}${MAGENTA}Building Viper dependencies...${NC}\n"
printf "Building libpmemobj-cpp\n"
cd $VERIF_STORAGE_DIR/evaluation/viper_deps/libpmemobj-cpp
mkdir -p build
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=./build
make
make install

printf "Building benchmark\n"
cd $VERIF_STORAGE_DIR/evaluation/viper_deps/benchmark
cmake -E make_directory "build"
cmake -DBENCHMARK_DOWNLOAD_DEPENDENCIES=on -DCMAKE_BUILD_TYPE=Release -S . -B "build" -DBUILD_SHARED_LIBS=ON
cmake --build "build" --config Release
sudo cmake --build "build" --config Release --target install
printf "${BOLD}${MAGENTA}Done building Viper dependencies!${NC}\n\n\n"

# 14. Build Viper wrapper
step; printf "${BOLD}${MAGENTA}Building Viper wrapper...${NC}\n"
cd $VERIF_STORAGE_DIR/evaluation/viper_wrapper
make all JAVA_HOME=$JAVA_HOME
printf "${BOLD}${MAGENTA}Done building Viper wrapper!${NC}\n\n\n"

printf "${BOLD}${MAGENTA}Done! Please run \'source ~/.bashrc\' to complete setup.${NC}\n"