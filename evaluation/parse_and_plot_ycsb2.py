import csv
import sys
import os
import matplotlib.pyplot as plt
import numpy as np

thread_counts = [1, 2, 4, 8]
# TODO: add run d
workloads = ['Loada', 'Runa', 'Runb', 'Runc', 'Rund', 'Loade', 'Runf', 'Loadx', 'Runx']
workload_titles = ['LoadA', 'RunA', 'RunB', 'RunC', 'RunD', 'LoadE', 'RunF', 'LoadX', 'RunX']

def parse_data(fs, runs, result_dir):
    raw_results = {w: {} for w in workloads}
    avg_results = {w: {} for w in workloads}

    # read in all data
    for w in workloads:
        for t in thread_counts:
            raw_results[w][t] = {}
            if t > 2:
                # TODO: remove
                raw_results[w][t] = {f: [0] for f in fs}
                continue
            for f in fs:
                run_dir = os.path.join(result_dir, "threads_" + str(t), f, w)
                raw_results[w][t][f] = []

                if w == "Rund":
                    # TODO REMOVE
                    continue

                for i in runs:
                   run_file = os.path.join(run_dir, "Run" + str(i))
                   with open(run_file, "r") as fp:
                       lines = fp.readlines()
                       for line in lines:
                           if "(ops/sec)" in line:
                               words = line.split()
                               perf = round(float(words[2]), 2)
                               raw_results[w][t][f].append(perf)
    
    # take the average of each workload at each number of threads
    for w in workloads:
        for t in thread_counts:
            avg_results[w][t] = []
            for f in fs:
                if w == "Rund":
                    # TODO REMOVE
                    avg_results[w][t].append(0)
                else:
                    avg_results[w][t].append(sum(raw_results[w][t][f]) / len(raw_results[w][t][f]))

    return avg_results

def plot_data(fs, avg_results, output_file):
    vert = 3
    horiz = 3

    print(avg_results)

    fig, ax = plt.subplots(vert, horiz)
    w_index = 0

    for i in range(0, vert):
        for j in range(0, horiz):
            workload = workloads[w_index]
            avg_results[workload]

            values = []
            for t in thread_counts:
                values.append([v / 1000 for v in avg_results[workload][t]])
            ax[i][j].set_prop_cycle(color=["blue", "orange", "black"], marker=['o', 'x', '+'])
            ax[i][j].plot(thread_counts, values)
            ax[i][j].set_xticks(thread_counts)
            ax[i][j].sharey(ax[0][0])
            ax[i][j].set_ylim(top=300)
            ax[i][j].set_title(workload_titles[w_index])
            ax[i][j].set_axisbelow(True)
            
            w_index += 1

    fig.tight_layout()
    fig.subplots_adjust(top=0.85)
    fig.legend(fs, loc="upper center", bbox_to_anchor=(0.5, 1), ncols=3)
    plt.savefig(output_file, format="pdf")


def main():
    if len(sys.argv) < 6:
        print("Usage: python3 parse_ycsb2.py <num_fs> <fs1> <fs2> .. <num_runs> <start_run_id> <result_dir> <output_file>")
        return

    args = sys.argv[1:]

    num_fs = int(args[0])
    fs = []
    for i in range(0, num_fs):
        fs.append(args[i+1])

    num_runs = int(args[num_fs+1])
    start_run_id = int(args[num_fs+2])
    result_dir = args[num_fs+3]
    output_file = args[num_fs+4]

    runs = []
    for i in range(start_run_id, start_run_id + num_runs):
        runs.append(i)

    avg_results = parse_data(fs, runs, result_dir)
    plot_data(fs, avg_results, output_file)

main()