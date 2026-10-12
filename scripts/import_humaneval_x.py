"""Turn the Rust part of HumanEval-X (THUDM/CodeGeeX, humaneval_rust.jsonl.gz) into one
library crate per problem: declaration + canonical solution (tests are not included).

usage: python3 -I import_humaneval_x.py humaneval_rust.jsonl.gz OUT_DIR
"""
import gzip
import json
import os
import re
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
EXTERNAL = re.compile(r"^\s*use\s+(rand|regex|md5)\b.*$", re.M)
with gzip.open(src, "rt") as f:
    for line in f:
        d = json.loads(line)
        num = int(d["task_id"].split("/")[1])
        decl = EXTERNAL.sub("", d["declaration"])
        m = re.search(r"fn\s+([a-zA-Z0-9_]+)", decl)
        name = m.group(1) if m else "main"
        body = (
            f"// HumanEval-X {d['task_id']} (declaration + canonical solution)\n"
            "#![allow(unused, deprecated)]\n"
            + decl
            + d["canonical_solution"]
            + "\n"
        )
        with open(os.path.join(out, f"he{num:03d}_{name}.rs"), "w") as g:
            g.write(body)
