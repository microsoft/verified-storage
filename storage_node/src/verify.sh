#!/bin/bash

VERUS_PATH=/home/$USER/verus/source/target-verus/release/verus

clear
$VERUS_PATH lib.rs --compile --expand-errors -L dependency=../../deps_hack/target/debug/deps --extern=deps_hack=../../deps_hack/target/debug/libdeps_hack.rlib $@