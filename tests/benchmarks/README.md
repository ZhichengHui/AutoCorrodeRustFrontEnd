# Benchmark suites

Each `.rs` file (or each directory with a `lib.rs`) is compiled as a separate library crate
by `scripts/run_benchmarks.sh SUITE`. The suites were imported with
`scripts/import_humaneval_x.py` and `scripts/import_benchmarks.py`.

| Suite | Source | Crates | Licence |
|---|---|---|---|
| `aeneas` | `tests/src` of [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas), commit `d119a474f852781f8ae88a85424f2f8ba8407b82`; the crates `avl`, `bst`, `tutorial` flattened to one file | 113 | Apache-2.0 |
| `charon` | `charon/tests/ui/**` of [AeneasVerif/charon](https://github.com/AeneasVerif/charon), commit `0a930b2dacb98daa0cad6558d2e0b8451e355b64`; file `DIR/NAME.rs` becomes `DIR__NAME.rs` | 467 | Apache-2.0 |
| `humaneval_x` | Rust part of HumanEval-X ([THUDM/CodeGeeX](https://github.com/THUDM/CodeGeeX), `codegeex/benchmark/humaneval-x/rust/data/humaneval_rust.jsonl.gz`): declaration + canonical solution of each problem; the `use` lines of the external crates `rand`, `regex`, `md5` are removed | 164 | Apache-2.0 |
| `algorithms` | [TheAlgorithms/Rust](https://github.com/TheAlgorithms/Rust), commit `fed66cb0c74c4a939ec5163648458a8c2b46fd4c`: the 347 files of `src/` that use no other module and no external crate | 347 | MIT |
| `crust` | CRUST-bench ([anirudhkhatry/CRUST-bench](https://github.com/anirudhkhatry/CRUST-bench), `datasets/CRUST_bench.zip`, `RBench`): commit `4b4702544b800a3821feea128c5b9e413665dc83`: the 77 projects without dependencies; `src/interfaces/*.rs` moved next to `lib.rs`. Function bodies are `unimplemented!()` (the benchmark asks for them), so this suite mainly exercises types and multi-module crates. **Not committed** (GPL-3.0): import it with `python3 -I scripts/import_benchmarks.py crust CRUST_bench.zip tests/benchmarks/crust` | 77 | GPL-3.0 |

Files that rustc itself rejects are reported as `rustc-rejected`: negative borrow-checking
tests (Aeneas, Charon), Charon tests that need an auxiliary crate, and the two HumanEval-X
problems that need the crates `regex` and `md5`.
