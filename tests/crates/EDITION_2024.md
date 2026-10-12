# Edition 2024 edits

The crates are compiled with `--edition=2024`. These upstream files were written for
edition 2021; each edit below is the smallest one rustc accepts under 2024 and keeps the
program's meaning. All other files are byte-identical to upstream.

| File | Line | 2024 rule | Edit |
|---|---|---|---|
| `charon__issue_73_extern.rs` | 2 | `extern` blocks must be `unsafe` | `extern "C"` → `unsafe extern "C"` |
| `charon__regressions__extern_static_no_initializer_aux.rs` | 2 | same | same |
| `charon__simple__extern_same_name_across_modules.rs` | 1 | same | same |
| `charon__variadics.rs` | 9 | same | same |
| `algorithms__math__field.rs` | 236–242 | `gen` is a reserved keyword | identifier `gen` → `r#gen` |
| `algorithms__data_structures__binary_search_tree.rs` | 83 | no explicit `ref`/`ref mut` under an implicit borrow | `Some(ref mut node)` → `Some(node)` (the scrutinee is `&mut Option<_>`, so `node` is still `&mut`) |
| `algorithms__graph__page_rank.rs` | 80 | no `&` pattern under an implicit borrow | `\|(_, &degree)\|` → `\|&(_, &degree)\|` |
| `algorithms__string__manacher.rs` | 67 | same | `\|(_, &value)\|` → `\|&(_, &value)\|` |
| `charon__statics.rs` | 2 | lint `static_mut_refs` is deny-by-default | added `#![allow(static_mut_refs)]`; the file tests references to a `static mut`, so the code is kept |
