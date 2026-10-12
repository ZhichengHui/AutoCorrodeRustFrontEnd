# urust-frontend

Translates the HIR of a Rust library crate into AutoCorrode µRust theories.
Constructs that µRust cannot express become placeholders, so the output is always a
complete theory set that Isabelle accepts.

## Requirements

| Item | Version |
|---|---|
| rustc (with `rustc-dev`) | `rustc 1.100.0-nightly (923c95cdf 2026-09-16)` = toolchain `nightly-2026-09-17` |
| AutoCorrode | `main` (200f1ac) + branch `signed-integers` (c834d8e) + branch `urust-break-continue` (fca2291), merged |
| Isabelle | Isabelle2025-2 |

`scripts/cargo.sh` and `scripts/urust-frontend.sh` use the toolchain under
`~/Work/aeneas-env` (override with `RUSTUP_HOME` / `CARGO_HOME`).

## Usage

```
scripts/cargo.sh build
scripts/urust-frontend.sh [--out DIR] [--name NAME] [--parent SESSION] FILE.rs [-- RUSTC-ARGS...]
```

The crate is compiled as a library (default edition 2024). For crate `NAME` the output directory contains:

| File | Content |
|---|---|
| `NAME_TypesExternal_Template.thy` | `typedecl`s for external types (e.g. `HashMap`) and placeholder types (e.g. `f64`) |
| `NAME_Types.thy` | structs (`datatype_record` + `micro_rust_record`) and enums (`datatype`), constructor functions |
| `NAME_Locale.thy` | locale `NAME_ctx`: `reference` + one `reference_allocatable` per type of a mutable local, fuel `urust_fuel` |
| `NAME_FunsExternal_Template.thy` | template definitions (`unimplemented!` bodies) for called functions defined outside the crate |
| `NAME_FunsForeign_Template.thy` | template definitions for functions of `extern` blocks |
| `NAME_Funs.thy` | all functions, methods and constants of the crate, in dependency order |
| `ROOT` | session `NAME` with parent `AutoCorrode` |
| `PLACEHOLDERS.txt` | every placeholder with its source line |

## Translation scheme

| Rust | µRust / HOL |
|---|---|
| path `m::Type::f` | HOL constant `m_Type_f` (modules flattened; nested items moved to top level) |
| `u8`…`u64`, `usize` / `i8`…`i64`, `isize` | `8 word`…`64 word` / `8 sword`…`64 sword` |
| `bool`, `char`, `&str`, `String` | `bool`, `char`, `String.literal` |
| `[T; n]`, `[T]`, `Vec<T>` | `T list` |
| tuple `(A, B)`, `()` | `A × B × tnil`, `unit` |
| `Option`, `Result`, `Box<T>` | `option`, `result`, `T` |
| `&T` | `T` (shared borrows are values) |
| `&mut T` | `('addr, 'gv, T) Global_Store.ref` |
| `let mut x = e` | µRust mutable local (allocated reference); reads are `*x` |
| field `p.f` of struct `S` | lens field `p.S_f` (on values and on references) |
| method call `x.m(a)` | call `S_m(x, a)` of the resolved function |
| `while`, `loop` | `#[fuel(ε‹urust_fuel›)] while/loop` |
| `for x in a..b` / over a slice or `Vec` | µRust `for` |
| recursion (each strongly connected component of the call graph) | `fun f_fuel :: nat ⇒ …` with `f ≡ f_fuel urust_fuel` |
| `match` on integers / chars / strings | `if` chain on a temporary |
| literal or range sub-pattern | fresh binder + match guard |
| `x /= e`, `S { f: e, ..base }`, `let S { f, .. } = e` | desugared |
| unsupported construct | `unimplemented!("UNSUPPORTED …")` (expression), template, or `typedecl` |

## Tests

```
scripts/run_tests.sh            # translate tests/cases/*.rs and build session Frontend_Tests
NO_ISABELLE=1 scripts/run_tests.sh   # translation only
```

The Isabelle build runs under `systemd-run … MemoryMax=4G` and needs the heap of
session `AutoCorrode` built from the merged AutoCorrode checkout (`AUTOCORRODE`).
