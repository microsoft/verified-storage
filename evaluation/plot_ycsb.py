#!/bin/python3 

import matplotlib.pyplot as plt
import matplotlib.pylab as pylab
import csv
import numpy as np
import sys

ycsb_run_names = ["LoadA", "RunA", "RunB", "RunC", "RunD", "LoadE", "RunF", "LoadX", "RunX"]
ycsb_runs = {"Loada": [], "Runa": [], "Runb": [], "Runc": [], "Rund": [], "Loade": [], "Runf": [], "Loadx": [], "Runx": []}
kv_stores = ["redis", "RocksDB", "CapybaraKV"]
legend_names = ["pmem-Redis", "pmem-RocksDB", "CapybaraKV"]

def plot_ycsb(ax, ycsb_results_file):
    with open(ycsb_results_file, "r") as f:
        reader = csv.reader(f)
        current_run = ""
        for row in reader:
            if len(row) == 0:
                continue 
            elif row[0] in ycsb_runs:
                current_run = row[0]
            elif row[0] == "":
                data = [float(x) for x in row[1:5]]
                ycsb_runs[current_run] = data

    print(ycsb_runs)

    filesys_grouped_data = {k:[] for k in kv_stores}
#     filesys_raw_grouped_data = {k:[] for k in kv_stores}
    for run in ycsb_runs:
        data = ycsb_runs[run]

        filesys_grouped_data["redis"].append(data[0] / 1000)
        filesys_grouped_data["RocksDB"].append(data[1] / 1000)
        filesys_grouped_data["CapybaraKV"].append(data[2] / 1000)

#         ext4_baseline = data[0]
#         # calculate throughput wrt ext4 baseline so that everything
#         # will fit on the same graph
#         nova = data[1] / ext4_baseline
#         winefs = data[2] / ext4_baseline 
#         squirrelfs = data[3] / ext4_baseline

#         filesys_raw_grouped_data["Ext4-DAX"].append(data[0])
#         filesys_raw_grouped_data["NOVA"].append(data[1])
#         filesys_raw_grouped_data["WineFS"].append(data[2])
#         filesys_raw_grouped_data["SquirrelFS"].append(data[3])

#         filesys_grouped_data["Ext4-DAX"].append(1)
#         filesys_grouped_data["NOVA"].append(nova)
#         filesys_grouped_data["WineFS"].append(winefs)
#         filesys_grouped_data["SquirrelFS"].append(squirrelfs)

    # params = {'legend.fontsize': 'large',
    #     'axes.labelsize': 'x-large',
    #     'axes.titlesize':'large',
    #     # 'xtick.labelsize':'large',
    #     'ytick.labelsize':'large'}
    # pylab.rcParams.update(params)

    print(filesys_grouped_data["redis"])

    normalized_data_redis = [ 1 for i in range(0, len(filesys_grouped_data["redis"]))]
    normalized_data_rocksdb = [ filesys_grouped_data["RocksDB"][i] / filesys_grouped_data["redis"][i] for i in range(0, len(filesys_grouped_data["RocksDB"]))]
    normalized_data_capybarakv = [ filesys_grouped_data["CapybaraKV"][i] / filesys_grouped_data["redis"][i] for i in range(0, len(filesys_grouped_data["CapybaraKV"]))]
    

    x = np.arange(len(ycsb_run_names))

    width = 0.25

    # fig, ax = plt.subplots()

    r1 = ax.bar(x-width*1, normalized_data_redis, width, hatch="//", color="cornflowerblue")
    autolabel(ax, r1, filesys_grouped_data["redis"])
    r2 = ax.bar(x-width*0, normalized_data_rocksdb, width, hatch="..", color="orange")
    # autolabel(ax, r2, filesys_grouped_data["RocksDB"])
    r3 = ax.bar(x+width*1, normalized_data_capybarakv, width, color="black")
    # autolabel(ax, r3, filesys_grouped_data["CapybaraKV"])
    # ax.grid(True, zorder=0)
    # fig.set_figwidth(6.9)
    # fig.set_figheight(2.25)
    ax.set_axisbelow(True)
    ax.grid(True, zorder=0, axis="y")

    ax.set_xticks(x, ycsb_run_names)
    # ax.set_ylabel("kops/s (relative)")
    # ax.set_xlabel("YCSB workloads")
    
    # plt.ylim(0,26)
    

def autolabel(ax, rects, data):
    i = 0
    for rect in rects:
        throughput = data[i]
        ax.annotate("{}".format(int(round(throughput, 0))),
            xy=(rect.get_x() + rect.get_width() / 2, rect.get_height()),
            rotation=90,
            ha="center", va="bottom",
            fontsize=10
            )
        i += 1

def plot_ycsb_all(ycsb_results_file_1thread, ycsb_results_file_16thread, output_file):
    fig, axs = plt.subplots(1, 2)

    plot_ycsb(axs[0], ycsb_results_file_1thread)
    plot_ycsb(axs[1], ycsb_results_file_16thread)

    axs[0].set_ylim(0,22)
    axs[0].set_xlabel("(a) 1 thread")
    # axs[1].set_ylim(0,26)
    axs[1].set_xlabel("(b) 16 threads")
    axs[1].sharey(axs[0])
    axs[0].set_yticks([1, 5, 10, 15, 20])

    axs[0].set_ylabel("throughput relative to pmem-Redis")

    fig.set_figwidth(10)
    fig.set_figheight(2.5)
    # fig.legend(legend_names, ncol=3, loc="upper center", bbox_to_anchor=(0.5,1.2))
    fig.legend(legend_names, ncol=3, loc="upper center", bbox_to_anchor=(0.5,1.1))
    fig.tight_layout(pad=0.75)
    plt.savefig(output_file, format="pdf", bbox_inches="tight")

def main():
    if len(sys.argv) < 3:
        print("Too few arguments")
        exit(1)
    ycsb_results_file_1thread = sys.argv[1]
    ycsb_results_file_16thread = sys.argv[2]
    output_file = sys.argv[3]

    plot_ycsb_all(ycsb_results_file_1thread, ycsb_results_file_16thread, output_file)


main()