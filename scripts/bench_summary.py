"""Summarise a benchmark run: per crate translation status, placeholders, Isabelle result.

usage: python3 -I bench_summary.py OUT_DIR SUITE
"""
import os
import re
import sys

out, suite = sys.argv[1], sys.argv[2]
rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(out, "status.tsv")) if l.strip()]

log = ""
p = os.path.join(out, "isabelle.log")
if os.path.exists(p):
    log = open(p, encoding="utf-8", errors="replace").read()
errs = ""
p = os.path.join(out, "isabelle_errors.log")
if os.path.exists(p):
    errs = open(p, encoding="utf-8", errors="replace").read()

# first error message per crate directory
first_err = {}
blocks = re.split(r"\n(?=\*\*\* )", errs)
cur = []
for line in errs.splitlines():
    if not line.startswith("***"):
        continue
    cur.append(line[4:])
    m = re.search(r'At command .*?of "[^"]*/bench/' + re.escape(suite) + r'/([^/]+)/', line)
    if m:
        stem = m.group(1)
        if stem not in first_err:
            msg = " ".join(x.strip() for x in cur[:3])
            first_err[stem] = msg[:160]
        cur = []

rc = None
p = os.path.join(out, "isabelle.rc")
if os.path.exists(p):
    rc = open(p).read().strip()

counts = {}
lines = []
for stem, name, st, ph in rows:
    isa = "-"
    if st == "translated":
        # exit code 0: every theory was checked (possibly in an earlier, unchanged build)
        if rc == "0" or re.search(re.escape(name) + r"_Funs 100%", log):
            isa = "ok"
        elif log:
            isa = "FAILED"
        else:
            isa = "not run"
    key = (st, isa)
    counts[key] = counts.get(key, 0) + 1
    err = first_err.get(stem, "") if isa == "FAILED" else ""
    lines.append(f"| {stem} | {st} | {ph} | {isa} | {err.replace('|', '/')} |")

with open(os.path.join(out, "SUMMARY.md"), "w") as f:
    f.write(f"# Benchmark suite `{suite}`\n\n")
    f.write("| translation | Isabelle | crates |\n|---|---|---|\n")
    for (st, isa), n in sorted(counts.items()):
        f.write(f"| {st} | {isa} | {n} |\n")
    f.write("\n| crate | translation | placeholders | Isabelle | first Isabelle error |\n|---|---|---|---|---|\n")
    f.write("\n".join(lines) + "\n")
for (st, isa), n in sorted(counts.items()):
    print(f"{st:16} isabelle={isa:8} {n}")
