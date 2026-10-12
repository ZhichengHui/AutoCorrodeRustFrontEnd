"""Report the generated Funs theories with the deepest brace nesting.

usage: python3 -I nesting_depth.py out/bench/SUITE... [--top N]
"""
import glob
import os
import sys

args = [a for a in sys.argv[1:] if not a.startswith("--")]
top = 10
if "--top" in sys.argv:
    top = int(sys.argv[sys.argv.index("--top") + 1])
res = []
for out in args:
    for f in glob.glob(os.path.join(out, "*", "*", "*_Funs.thy")):
        depth = best = 0
        for ch in open(f, encoding="utf-8", errors="replace").read():
            if ch == "{":
                depth += 1
                best = max(best, depth)
            elif ch == "}":
                depth -= 1
        res.append((best, os.path.getsize(f), f))
for d, size, f in sorted(res, reverse=True)[:top]:
    print(f"{d:4} {size:8} {f}")
