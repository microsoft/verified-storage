#!/bin/bash

RED=$(tput setaf 1)
GREEN=$(tput setaf 2)
BOLD=$(tput bold)
NC=$(tput sgr0)
BG=${BOLD}${GREEN}

# 1. Install Rust and automatically select default installation
printf "${BOLD}Installing Rust...${NC}"
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
printf "${BG}Done installing Rust!${NC}"

# 2. Confirm that verified-storage crates build successfully
printf "${BOLD}Building verified-storage crates...${NC}"
cd ../deps_hack; cargo build --release
cd ../pmsafe; cargo build --release
cd ../storage_node/src; cargo build --release
printf "${BG}Done building verified-storage crates!${NC}"

# 3. Clone and build Verus
printf "${BOLD}Cloning and building Verus...${NC}"
cd ../../; git clone https://github.com/verus-lang/verus.git; cd verus/source/; source ../tools/activate; ./tools/get-z3.sh; vargo build --release
printf "${BG}Done building Verus!${NC}"

# 4. Confirm that CapybaraKV verifies
printf "${BOLD}Verifying CapybaraKV...${NC}"
cd ../storage_node/src/; ./verify.sh
printf "${BG}Done verifying CapybaraKV!${NC}"