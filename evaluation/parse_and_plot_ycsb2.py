import csv
import sys
import os
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import pprint

thread_counts = [1, 2, 4, 8, 16]
workloads = ['Loada', 'Runa', 'Runb', 'Runc', 'Rund', 'Loade', 'Runf', 'Loadx', 'Runx', "Runy", "Runz"]
workload_titles = ['LoadA', 'RunA', 'RunB', 'RunC', 'RunD', 'LoadE', 'RunF', 'LoadX', 'RunX', 'RunY', 'RunZ']
nice_names = {"redis": "pmem-Redis", "pmemrocksdb": "pmem-RocksDB", "capybarakv": "CapybaraKV"}

def parse_data(fs, runs, result_dir):
    raw_results = {w: {} for w in workloads}
    avg_results = {w: {} for w in workloads}

    # read in all data
    for w in workloads:
        for t in thread_counts:
            raw_results[w][t] = {}
            for f in fs:
                run_dir = os.path.join(result_dir, "threads_" + str(t), f, w)
                raw_results[w][t][f] = []

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
                avg_results[w][t].append(sum(raw_results[w][t][f]) / len(raw_results[w][t][f]))
    pprint.pprint(avg_results)

    return avg_results

def plot_data(fs, avg_results, output_file):
    vert = 3
    horiz = 3

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
            # ax[i][j].sharey(ax[0][0])
            # ax[i][j].set_ylim(top=300)
            ax[i][j].set_title(workload_titles[w_index])
            ax[i][j].set_axisbelow(True)
            ax[i][j].tick_params(axis="both", labelsize="10")
            
            w_index += 1

    fig.tight_layout()
    # fig.subplots_adjust(top=0.85)
    fig.supxlabel("Thread count", y=-0.01)
    fig.supylabel("Throughput (Kops/s)")
    fig.legend(fs, loc="upper center",  ncols=3)
    fig.set_figwidth(9.4)
    fig.set_figheight(4)
    plt.subplots_adjust(left=0.08, top=0.85, bottom=0.1)

    plt.savefig(output_file, format="pdf", bbox_inches="tight")

def plot_data_single_fig(fs, avg_results, output_file):
    plt.plot()

    values = []
    for t in thread_counts:
        thread_vals = []
        for w in workloads:
            thread_vals.append(avg_results[w][t][0] / 1000000)
        values.append(thread_vals)

    fig, ax = plt.subplots()

    color_cycle = plt.rcParams['axes.prop_cycle'].by_key()['color']
    ax.set_prop_cycle(
        color=color_cycle+["black"], 
        marker=["o", "x", "s", "d", "+", "v", "^", "p", ".", "o", "x"],
        linestyle=["-", "-", "-", "-", "-", "-", "--", "--", "--", "--", "--"]
    )
    ax.plot(thread_counts, values)
    ax.set_xticks(thread_counts)
    ax.legend(workload_titles, loc="center right", bbox_to_anchor=(1.35, 0.5))
    ax.set_xlabel("Thread count")
    ax.set_ylabel("Througput (Mops/s)")
    

    fig.set_figwidth(5)
    fig.set_figheight(2)
    fig.tight_layout(pad=0)
    ax.grid(True, zorder=0, axis="y")
    # plt.gca().yscale("log")
    # plt.yscale("log")
    # plt.yticks([500,1000,1500,2000,2500,3000,3500,4000])
    # formatter = matplotlib.ticker.ScalarFormatter()
    # formatter.set_powerlimits((0,3))
    # plt.gca().yaxis.set_major_formatter(formatter)
    

    plt.savefig(output_file, format="pdf", bbox_inches="tight")


def main():
    if len(sys.argv) < 6:
        print("Usage: python3 parse_and_plot_ycsb2.py <num_fs> <fs1> <fs2> .. <num_runs> <start_run_id> <result_dir> <output_file>")
        return

    args = sys.argv[1:]

    num_fs = int(args[0])
    fs = []
    for i in range(0, num_fs):
        fs.append(args[i+1])
    fs_nice = [nice_names[f] for f in fs]

    num_runs = int(args[num_fs+1])
    start_run_id = int(args[num_fs+2])
    result_dir = args[num_fs+3]
    output_file = args[num_fs+4]

    runs = []
    for i in range(start_run_id, start_run_id + num_runs):
        runs.append(i)

    avg_results = parse_data(fs, runs, result_dir)
    plot_data_single_fig(fs_nice, avg_results, output_file)

main()