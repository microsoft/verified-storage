import sys
import re
import subprocess
import json
from prettytable import PrettyTable
import argparse
import os

# TODO: this script should properly handle things if the _t files don't have the 
# trusted annotations (or if they're commented out)

categories = ["PoWER framework", "pmcopy crate", "Base log", "KV store"]
line_types = ["Trusted", "Spec+Proof", "Impl"]

def split_line(line):
    line = line.split("|")
    line = [l.rstrip().lstrip() for l in line]
    return line

def extract_line_counts(headers, line):
    raw_loc = {}
    for h, c in zip(headers, line):
        if len(h) != 0 and h != "file":
            raw_loc[h] = int(c)
    
    # clean up to only include the stats we are interested in
    # From Andrea, same accounting used in SOSP Verus paper:
    # let proof = output.total.proof + output.total.spec + output.total.proof_exec;
    # let exec = output.total.exec + output.total.proof_exec;

    loc = {l: 0 for l in line_types} 
    loc["Trusted"] = raw_loc["Trusted"]
    loc["Spec+Proof"] = raw_loc["Spec"] + raw_loc["Proof"] + raw_loc["Proof+Exec"]
    loc["Impl"] = raw_loc["Exec"] + raw_loc["Proof+Exec"]

    return loc
            

def count_lines(line_count_file):
    header_pattern = "Trusted"
    power_pattern = "pmem/"
    log_pattern = "journal/"
    headers = []

    results = {k: {l: 0 for l in line_types} for k in categories}

    with open(line_count_file, "r") as f:
        for line in f:
            if "----" in line or "total" in line:
                continue
            if header_pattern in line:
                headers = split_line(line)
            else:
                if power_pattern in line:
                    line = split_line(line)
                    loc = extract_line_counts(headers, line)
                    for k in loc.keys():
                        results["PoWER framework"][k] += loc[k]
                elif log_pattern in line:
                    line = split_line(line)
                    loc = extract_line_counts(headers, line)
                    for k in loc.keys():
                        results["Base log"][k] += loc[k]
                else: # everything else is kv
                    line = split_line(line)
                    loc = extract_line_counts(headers, line)
                    for k in loc.keys():
                        results["KV store"][k] += loc[k]
    
    return results

def count_pmcopy_lines(pmcopy_directory):
    # pmcopy is in a separate crate so we'll handle it separately
    # TODO: tokei install instructions or use a different tool
    # TODO: change name of the crate
    output = subprocess.check_output(["tokei", pmcopy_directory, "--output", "json"])
    output_dict = json.loads(output)
    return output_dict["Rust"]["code"]

def build_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", help=".d file emitted by invoking Verus with `--emit=dep-info`.")
    parser.add_argument("pmcopy_path", help="Path to pmcopy crate root.")
    parser.add_argument("verus_path", help="Path to Verus source code directory.")
    parser.add_argument("--line_count_file", required=False, type=str, default="line_count.txt", help="File to store intermediate line count output in.")
    return parser

def main():
    parser = build_parser()
    args = parser.parse_args()

    d_file = args.input_file
    pmcopy_directory = args.pmcopy_path
    verus_path = args.verus_path
    line_count_file = args.line_count_file

    cwd = os.getcwd()
    
    input_file_full_path = os.path.join(cwd, d_file)
    print(input_file_full_path)

    # call the verus line count tool on the provided .d file
    with open(line_count_file, "w") as f:
        subprocess.check_call(
            ["cargo", "run", "--release", "--", input_file_full_path], 
            cwd=os.path.join(verus_path, "source", "tools", "line_count"), 
            stdout=f
        );

    kv_lines = count_lines(line_count_file)
    pmcopy_lines = count_pmcopy_lines(pmcopy_directory)

    table = PrettyTable()
    table.field_names = [""] + line_types
    trusted_total = 0
    proof_total = 0
    exec_total = 0
    for k in kv_lines.keys():
        counts = []
        if k == "pmcopy crate":
            counts = [pmcopy_lines, 0, 0]
            trusted_total += pmcopy_lines
        else:
            counts = [kv_lines[k][l] for l in line_types]
            trusted_total += kv_lines[k]["Trusted"]
            proof_total += kv_lines[k]["Spec+Proof"]
            exec_total += kv_lines[k]["Impl"]
        table.add_row([k] + counts)
    table.add_row(["Total", trusted_total, proof_total, exec_total])
    print(table)

    pc_ratio = proof_total / exec_total
    print("Proof to code ratio: " + str(pc_ratio))

main()