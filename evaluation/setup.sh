#!/bin/bash

# 1. Install Rust and automatically select default installation
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"

# 2. Confirm that verified-storage crates build successfully
cd ../deps_hack; cargo build --release
cd ../pmsafe; cargo build --release
cd ../storage_node/src; cargo build --release

# 3. Clone and build Verus
cd ../../; git clone git@github.com:verus-lang/verus.git; cd verus/source/; source ../tools/activate; ./tools/get-z3.sh; vargo build --release

# 4. Confirm that CapybaraKV verifies
cd ../storage_node/src/; ./verify.sh