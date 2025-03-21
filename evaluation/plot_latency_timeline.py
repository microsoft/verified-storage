import matplotlib.pyplot as plt
import numpy as np
import sys
import re

# this script is for parsing files that have output from 
# YCSB's `measurementtype=raw` option for reporting latency

ops = ["INSERT", "UPDATE", "READ"]
events = {"flush_started": "red", "flush_finished": "green",
        "compaction_started": "purple", "compaction_finished": "yellow"}
        
        # "table_file_deletion": "yellow", "table_file_creation": "orange"}

def read_data(input_file):
    results = {}
    # base_time = 0

    with open(input_file, "r") as f:
        lines = f.readlines()
        count = 0
        for line in lines:
            words = line.rstrip().split(",")
            op = words[0]
            if op in ops:
                # if count % 10000 == 0:
                time = int(words[1])
                # if base_time == 0:
                #     base_time = time
                latency = words[2]
                if op not in results.keys():
                    results[op] = [(time, int(latency))]
                else:
                    results[op].append((time, int(latency)))
                count +=1
    
    return results

def read_pmemrocksdb_log(pmemrocksdb_log_file):
    event_timestamps = []
    with open(pmemrocksdb_log_file, "r") as f:
        lines = f.readlines()
        for line in lines:
            for e in events.keys():
                if e in line:
                    pattern = "\"time_micros\": ([0-9]+)"
                    match = re.search(pattern, line)
                    timestamp = int(match.group(1)) / 1000
                    event_timestamps.append((e, timestamp))
    return event_timestamps

def plot_data(results, output_file, event_timestamps):
    fig, ax = plt.subplots(len(results))

    for i, k in enumerate(results):
        timestamps = [v[0] for v in results[k]]
        data = [v[1] for v in results[k]]

        if len(results) == 1:
            cur_ax = ax
        else:
            cur_ax = ax[i]

        cur_ax.plot(timestamps, data)
        cur_ax.set_yscale("log")
        cur_ax.set_title(k)

        if event_timestamps != None:
            for e in event_timestamps:
                event = e[0]
                timestamp = e[1]
                if timestamps[0] <= timestamp and timestamp <= timestamps[len(timestamps)-1]:
                    print(e)
                    cur_ax.axvline(x=timestamp, color=events[event])

        if len(results) == 1:
            break


        # if compaction_timestamps != None:
        #     # ax.vlines(compaction_timestamps, 0, max(data))
        #     for timestamp in compaction_timestamps:
        #         if timestamp < timestamps[len(timestamps)-1]:
        #             ax.axvline(x=timestamp, color="red")
        # if flush_timestamps != None:
        #     # ax.vlines(compaction_timestamps, 0, max(data))
        #     for timestamp in flush_timestamps:
        #         if timestamp < timestamps[len(timestamps)-1]:
        #             ax.axvline(x=timestamp, color="green")

        # # moving average
        # window_width = 10000
        # cumsum_vec = np.cumsum(np.insert(data, 0, 0)) 
        # ma_vec = (cumsum_vec[window_width:] - cumsum_vec[:-window_width]) / window_width

        # print(len(data))
        # print(len(ma_vec))
        # axs[i+1].plot(ma_vec)
        # # axs[i].plot(timestamps, data)
        # axs[i+1].set_yscale("log")

    fig.set_figwidth(24)
    
    plt.savefig(output_file, format="pdf")

def main():
    if len(sys.argv) < 3:
        print("Usage: python3 plot_latency_timeline.py <input_file>  <output_file>")
    args = sys.argv[1:]

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    if len(sys.argv) == 4:
        pmemrocksdb_log_file = sys.argv[3]
        event_timestamps = read_pmemrocksdb_log(pmemrocksdb_log_file)
    else:
        event_timestamps = None

    results = read_data(input_file)
    plot_data(results, output_file, event_timestamps)

main()