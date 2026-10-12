# 测试

唯一的测试入口是 `tests/frontend.rs` 中的 `crates()`。它逐个翻译 `tests/crates/*.rs`，再用一个有内存上限的 Isabelle server 逐个检查，最后按以下 6 类报告每个 crate 的结果和各类数量：rustc 拒绝、前端崩溃、Isabelle 拒绝、未完成（超时或超出内存）、接受且有占位符、接受且无占位符。测试只报告结果，不断言预期。

## 准则

1. **先定位根因再动手。** 出现问题时，先用一两句话说明根本原因，再改前端。不为让某个测试通过而改测试、删用例，或在前端里特判。
2. **测试要最小、可复现。** 每个用例是 `tests/crates` 中一个独立的 `.rs` 文件，作为 library crate 编译，用 rustc `--edition=2024` 能通过。它不依赖其他用例、全局状态或执行顺序。
3. **只有一个测试文件。** 新用例只往 `tests/crates` 里加 crate，不新增测试文件、辅助脚本、fixture 或说明文档。确实需要的公共数据放在 `tests/frontend.rs` 顶部。
4. **不写补丁式文档。** 不新增 README、CHANGELOG 或"修复说明"之类的文档，除非用户明确要求。

## 语料

- 文件名格式为 `来源__原路径.rs`（原路径中的 `/` 换成 `__`）。外部来源有 aeneas、charon 和 TheAlgorithms/Rust；手写的用例以 `handwritten__` 开头。
- 外部来源的文件与上游逐字节一致。唯一允许的修改是 edition 2024 要求的最小语法修改，每一处都记录在 `crates/EDITION_2024.md` 中。
- 收录规则只有一条：rustc 用 `--edition=2024 --crate-type=lib` 能编译。不因为前端或 Isabelle 的结果而增删用例。

## 运行

```
AUTOCORRODE=<AutoCorrode checkout> [MEMORY_MAX=4G] [CRATE_FILTER=<文件名片段>] \
  scripts/cargo.sh test --release -- --nocapture
```

先用 `CRATE_FILTER` 只跑一个 crate。跑完整语料前，先和用户约定内存预算。
