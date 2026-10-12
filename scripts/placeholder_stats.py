"""Placeholder statistics of benchmark runs.

usage: python3 -I placeholder_stats.py out/bench/SUITE...
"""
import collections
import glob
import os
import re
import sys

kinds = collections.Counter()
for out in sys.argv[1:]:
    rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(out, "status.tsv")) if l.strip()]
    tr = [r for r in rows if r[2] == "translated"]
    zero = sum(1 for r in tr if r[3] == "0")
    total = sum(int(r[3]) for r in tr)
    print(f"{os.path.basename(out)}: translated={len(tr)} without-placeholders={zero} placeholders={total}")
    for f in glob.glob(os.path.join(out, "*", "*", "PLACEHOLDERS.txt")):
        for line in open(f):
            if line.startswith("- "):
                k = re.sub(r"^- line \d+: ", "", line.strip())
                k = re.sub(r" -- .*$", "", k)
                k = re.sub(r"`[^`]*`", "`..`", k)
                kinds[k] += 1
print()
for k, n in kinds.most_common(30):
    print(f"{n:5}  {k}")
