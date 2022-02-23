
# Runs formula evaluation benchmark and aggregates the results

import os, sys, subprocess, re, argparse

parser= argparse.ArgumentParser()
parser.add_argument('path')
parser.add_argument('--flags')
args = parser.parse_args()

flags = args.flags
total = 0.0
for i in os.listdir(args.path):
    name = re.match("sep-(.*?).pickle", i)
    if not name: continue
    basename = name.group(1)
    cmdline = ['python3', 'src/mypyvy.py', 'fol-benchmark-sep', f'--expt-flags={flags}', '--query', os.path.join(args.path, i), f'examples/fol/{basename}.pyv']
    print(" ".join(cmdline))
    output = subprocess.check_output(cmdline, encoding='utf-8')
    for l in output.splitlines():
        if m := re.match("overall: ([0-9]+.[0-9]+)", l):
            time = float(m.group(1))
            print(basename, time)
            total += time
            break
    else:
        print("Warning: didn't find solution")
    
print(f"total: {total}")