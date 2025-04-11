#!/bin/bash

# This script updates the results directory, PM device, and mount point 
# for all config files in configs/. This approach is janky, but it is very 
# difficult to get all required information where it needs to go in the
# YCSB clients using command-line arguments, so we use a bunch of separate
# configuration files instead

RESULTS_DIR=$1
MOUNT_POINT=$2
PM_DEV=$3
ITERS=$4

if [ -z $RESULTS_DIR ]; then 
    echo "ERROR: Please specify a new results directory. Exiting."
    exit 
elif [ -z $MOUNT_POINT ]; then 
    echo "ERROR: Please specify a new mount point. Exiting."
    exit 
elif [ -z $PM_DEV ]; then 
    echo "ERROR: Please specify a new PM device. Exiting."
    exit
# elif [ -z $ITERS ]; then 
#     echo "ERROR: Please specify number of iterations. Exiting."
#     exit
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
if [[ "${MOUNT_POINT}" != *"/" ]]; then 
    MOUNT_POINT="${MOUNT_POINT}/"
fi

for filename in configs/*; do
    if [[ $filename != *"win"* ]]; then 
        # replacements in experiment configs
        sed -i "s!results_dir = \".*\"!results_dir = \"$RESULTS_DIR\"!" $filename
        sed -i "s!mount_point = \".*\"!mount_point = \"$MOUNT_POINT\"!" $filename
        sed -i "s!pm_device = \".*\"!pm_device = \"$PM_DEV\"!" $filename
        if [[ ! -z $ITERS && $filename != *"mini"* ]]; then 
            sed -i "s!iterations = .*!iterations = $ITERS!" $filename
        fi
        # replacements in capybarakv configs
        sed -i "s!kv_file = \".*\"!kv_file = \"$MOUNT_POINT/capybarakv\"!" $filename
    else 
        echo "Skipping windows config file ${filename}"
    fi
done