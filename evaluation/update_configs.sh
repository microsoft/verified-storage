#!/bin/bash

# This script updates the results directory, PM device, and mount point 
# for all config files in configs/. This approach is janky, but it is very 
# difficult to get all required information where it needs to go in the
# YCSB clients using command-line arguments, so we use a bunch of separate
# configuration files instead

RESULTS_DIR=$1
PM_DEV=$2
ITERS=$3

if [ -z $RESULTS_DIR ]; then 
    echo "ERROR: Please specify a new results directory. Exiting."
    exit 
elif [ -z $PM_DEV ]; then 
    echo "ERROR: Please specify a new PM device. Exiting."
    exit
fi

# if PM_DEV ends with a slash, remove it so that mkfs works properly
if [[ "$PM_DEV" == *"/" ]]; then 
    ${PM_DEV::-1}
fi  
# add trailing slash if not present for results_dir and mount_point
# makes them easier to deal with later
if [[ "${RESULTS_DIR}" != *"/" ]]; then 
    RESULTS_DIR="${RESULTS_DIR}/"
fi

for filename in configs/*; do
    if [[ $filename != *"win"* ]]; then 
        # replacements in experiment configs
        # sed -i "s!mount_point = \".*\"!mount_point = \"$MOUNT_POINT\"!" $filename
        sed -i "s!pm_device = \".*\"!pm_device = \"$PM_DEV\"!" $filename

        # mem storage files put output in a specific place
        if [[ $filename == *"mem_storage"* ]]; then 
            sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}mem_storage/\"!" $filename
        else 
            if [[ $filename == *"1.toml"* ]]; then 
                sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}threads_1\"!" $filename
            elif [[ $filename == *"2"* ]]; then
                sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}threads_2\"!" $filename
            elif [[ $filename == *"4"* ]]; then
                sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}threads_4\"!" $filename
            elif [[ $filename == *"8"* ]]; then
                sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}threads_8\"!" $filename
            elif [[ $filename == *"16"* ]]; then
                sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}threads_16\"!" $filename
            elif [[ $filename == *"microbenchmark"* ]]; then 
                sed -i "s!results_dir = \".*\"!results_dir = \"../${RESULTS_DIR}microbenchmark\"!" $filename
            else 
                sed -i "s!results_dir = \".*\"!results_dir = \"${RESULTS_DIR}\"!" $filename
            fi
        fi

        if [[ ! -z $ITERS && $filename != *"mini"* ]]; then 
            sed -i "s!iterations = .*!iterations = $ITERS!" $filename
        fi
    else 
        echo "Skipping windows config file ${filename}"
    fi
done