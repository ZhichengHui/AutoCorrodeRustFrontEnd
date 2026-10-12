"""Import benchmark sources into tests/benchmarks/SUITE.

usage:
  python3 -I import_benchmarks.py charon     CHARON_TESTS_UI_DIR   OUT_DIR
  python3 -I import_benchmarks.py algorithms THEALGORITHMS_SRC_DIR OUT_DIR
  python3 -I import_benchmarks.py crust      CRUST_bench.zip       OUT_DIR

charon:     every tests/ui/**/*.rs becomes one crate (SUBDIR__NAME.rs).
algorithms: every self-contained file of TheAlgorithms/Rust (no `crate::`/`super::` paths,
            no external crates) becomes one crate (CATEGORY__NAME.rs).
crust:      every CRUST-bench project (RBench) without dependencies becomes a crate
            directory PROJECT/ with lib.rs and its modules (src/interfaces/*.rs moved next
            to lib.rs, which is where `pub mod x;` looks for them).
"""
import os
import re
import shutil
import sys
import zipfile

kind, src, out = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)


def clean(name):
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


if kind == "charon":
    n = 0
    for root, _, files in os.walk(src):
        for f in sorted(files):
            if not f.endswith(".rs"):
                continue
            rel = os.path.relpath(os.path.join(root, f), src)
            parts = rel[:-3].split(os.sep)
            dst = os.path.join(out, "__".join(clean(p) for p in parts) + ".rs")
            shutil.copyfile(os.path.join(root, f), dst)
            n += 1
    print(f"charon: {n} files")

elif kind == "algorithms":
    EXTERNAL = re.compile(r"\b(crate::|super::|rand\b|nalgebra|ndarray|num_bigint|num_traits|quickcheck)")
    n = skipped = 0
    for root, _, files in os.walk(src):
        for f in sorted(files):
            if not f.endswith(".rs") or f in ("mod.rs", "lib.rs"):
                continue
            path = os.path.join(root, f)
            text = open(path).read()
            body = text.split("#[cfg(test)]")[0]
            if EXTERNAL.search(body) or re.search(r"^\s*mod\s+\w+\s*;", body, re.M):
                skipped += 1
                continue
            rel = os.path.relpath(path, src)[:-3].split(os.sep)
            dst = os.path.join(out, "__".join(clean(p) for p in rel) + ".rs")
            with open(dst, "w") as g:
                g.write("#![allow(unused, dead_code)]\n" + text)
            n += 1
    print(f"algorithms: {n} self-contained files, {skipped} skipped")

elif kind == "crust":
    z = zipfile.ZipFile(src)
    names = z.namelist()
    projects = sorted({n.split("/")[1] for n in names if n.startswith("RBench/") and n.count("/") > 1})
    n = skipped = 0
    for p in projects:
        try:
            cargo = z.read(f"RBench/{p}/Cargo.toml").decode()
        except KeyError:
            skipped += 1
            continue
        deps = cargo.split("[dependencies]")[1].split("\n[")[0] if "[dependencies]" in cargo else ""
        if re.search(r"^\s*[A-Za-z_]", deps, re.M) or f"RBench/{p}/src/lib.rs" not in names:
            skipped += 1
            continue
        d = os.path.join(out, clean(p))
        os.makedirs(d, exist_ok=True)
        for nm in names:
            pre = f"RBench/{p}/src/"
            if not nm.startswith(pre) or not nm.endswith(".rs") or "/bin/" in nm:
                continue
            rel = nm[len(pre):]
            if rel.startswith("interfaces/"):
                rel = rel[len("interfaces/"):]
            dst = os.path.join(d, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            with open(dst, "wb") as g:
                g.write(z.read(nm))
        n += 1
    print(f"crust: {n} projects without dependencies, {skipped} skipped")
