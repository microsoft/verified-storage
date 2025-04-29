#!/usr/bin/python

import sys
import os
import re
import subprocess

class DafnyFile:
  def __init__(self, filename):
    self.filename = filename.replace('\\', '/')
    self.trusted = 0
    self.proof = 0
    self.impl = 0

  def __repr__(self):
    return "%s %s trusted %s proof %s impl" % (self.filename, self.trusted, self.proof, self.impl)

  def is_trusted(self):
    return self.filename.endswith("_t.dfy")

def resolve_dafny(show_ghost, dafny_filename, tmp_filename):
  executable = "dafny"
  print_mode = "NoIncludes" if show_ghost else "NoGhostOrIncludes"
  args  = ["resolve", "--print", tmp_filename, "--print-mode", print_mode, dafny_filename]
  subprocess.call([executable] + args, shell=False)

def run_sloccount(tmp_dir):
  executable = "sloccount"
  args  = [] 
  args += ["--details"]
  args += [tmp_dir]

  sloc = -1
  #print [executable] + args
  output = subprocess.check_output([executable] + args) #, shell=True)
  output = output.decode("utf-8")
  for line in output.split('\n'):
    result = re.search("(\d+)\s+cs", line)
    if result:
      sloc = result.group(1)
  if sloc == -1:
    raise Exception("Failed to find sloccount result!")
  return sloc

def compute_sloc(show_ghost, dafny_file, tmp_dir):
  tmp_file = tmp_dir + "/tmp.dfy"
  tmp_file_cs = tmp_dir + "/tmp.cs"

  resolve_dafny(show_ghost, dafny_file, tmp_file)
  os.rename(tmp_file, tmp_file_cs)
  sloc = run_sloccount(tmp_dir)
  os.remove(tmp_file_cs)

  return int(sloc)

def collect_line_counts(dafny_files):
  tmp_dir = "/tmp/linecounts/"

  if not os.path.exists(tmp_dir):
    os.makedirs(tmp_dir)

  for (dirpath, dirnames, filenames) in os.walk(tmp_dir):
    for filename in filenames:
      print("Error: Directory %s where line counting will take place isn't empty: File %s already exists there" % (tmp_dir, os.path.join(dirpath, filename)))
      sys.exit(-1)
  
  for f in dafny_files:
    print("Processing %s" % f.filename)
    total_sloc = compute_sloc(True, f.filename, tmp_dir)

    if f.is_trusted():
      f.trusted = total_sloc
    else:
      impl_sloc = compute_sloc(False, f.filename, tmp_dir)
      f.impl = impl_sloc
      f.proof = total_sloc - impl_sloc

def define_categories():
  dir_categories = {\
    'src/Framework': 'framework',\
    'src/NotaryServer/': 'notary',\
    }

  return dir_categories

def categorize_files(dafny_files):
  categorized_files = {}
  dir_categories = define_categories()

  for dfile in dafny_files:
    best_match_prefix = ""
    best_match_cat = "Unknown"
    for prefix in dir_categories.keys():
      if dfile.filename.startswith(prefix) and len(prefix) > len(best_match_prefix):
        best_match_prefix = prefix
        best_match_cat = dir_categories[prefix]
    if not(best_match_cat in categorized_files):
      categorized_files[best_match_cat] = [dfile]
    else:
      categorized_files[best_match_cat] += [dfile]

  for cat in sorted(categorized_files.keys()):
    print()
    print(cat)
    print("-----------------------------")
    for f in categorized_files[cat]:
      print(f)

  return categorized_files

class SubTable:
  def __init__(self, name, row_names, allow_impl):
    self.name = name
    self.rows = row_names
    self.allow_impl = allow_impl

def amt(string, pos='c'):
  if int(string) == 0:
    return "--" 
  else:
    return string

def define_labels():
  labels = { 'framework': "Framework", 'notary': "Notary" }
  return labels

def table_label(key):
  labels = define_labels()
  if key in labels:
    return labels[key]
  else:
    return key

def build_table(categorized_files, latex_file):
  notary = SubTable("Notary Server", ['framework', 'notary'], allow_impl=True)

  tables = [notary]

  latex  = r"""
\begin{table}
    \begin{tabular}[pos]{l| r r r}
    \toprule
"""
  latex += r"& \multicolumn{1}{c}{\textbf{Spec}} & \multicolumn{1}{c}{\textbf{Proof}} & \multicolumn{1}{c}{\textbf{Impl}} \\" + "\n"
  latex += r"& \multicolumn{3}{c}{(source lines of code)} \\" + "\n"
  latex += "\n"
  latex += r"\midrule" + "\n\n"

  total_trusted_sloc = 0
  total_proof_sloc = 0
  total_impl_sloc = 0

  for subtable in tables:
    print()
    print(subtable.name)
    latex += "\\textbf{%s:} &&& \\\\\n" % (subtable.name)
    for row in subtable.rows:
      trusted_sloc = 0
      proof_sloc = 0
      impl_sloc = 0
      for file in categorized_files[row]:
        trusted_sloc += file.trusted
        proof_sloc += file.proof
        impl_sloc += file.impl
      if not(subtable.allow_impl):
        proof_sloc += impl_sloc
        impl_sloc = 0
      row_label = table_label(row)
      latex += "%s & %s & %s & %s \\\\\n" % (row_label, amt(trusted_sloc,'l'), amt(proof_sloc,'r'), amt(impl_sloc,'c'))

      total_trusted_sloc += trusted_sloc
      total_proof_sloc += proof_sloc
      total_impl_sloc += impl_sloc

    print()
    latex += "\\midrule\n"
    latex += "Total & %s & %s & %s \\\\\n" % (total_trusted_sloc, total_proof_sloc, total_impl_sloc)
    latex += r"""
    \bottomrule
    \end{tabular}
\end{table}
"""

  print()
  print(latex)
  latex_out = open(latex_file, "w")
  latex_out.write(latex)
  latex_out.close()


def main():
  output_file = "notary-line-counts.tex"
  input_dir = "src"
  print(f"Processing Dafny files in {input_dir}")
  files = []
  for (dirpath, dirnames, filenames) in os.walk(input_dir):
      for filename in filenames:
          if re.search(r"\.dfy$", filename):
              path = os.path.join(dirpath, filename)
              files.append(DafnyFile(path))
  collect_line_counts(files)
  cats = categorize_files(files)
  build_table(cats, output_file)
  print(f"LaTeX output saved to {output_file}")

main()
