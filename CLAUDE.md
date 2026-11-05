# urust-frontend

把 Rust library crate 的 HIR（rustc `1.100.0-nightly (923c95cdf 2026-09-16)`，edition 2024）翻译成 AutoCorrode 的 uRust theory。前端对各类 Rust 语言构造的处理记录在 `LANGUAGE_FEATURES.md`，标准库的等价模型记录在 `STD_MODELS.md`。

用 `scripts/cargo.sh` 构建，用 `scripts/urust-frontend.sh` 运行前端。

## 修改宗旨

1. **先定位根因再动手。** 先用一两句话写清问题的根本原因，再改代码。不为让某个输入通过而加条件分支、硬编码返回值或特判某个输入。
2. **判断依据来自编译器，不来自名字或文本。** 识别标准库条目用 lang item 或 diagnostic item，判断性质用类型、签名和 HIR 结构。不匹配名字、路径子串，也不匹配生成的 HOL 或 uRust 文本。
3. **不支持就输出占位符，并且登记。** 所有占位符都由 `Frontend::placeholder` 生成并登记到 `PLACEHOLDERS.txt`。丢弃或简化 Rust 语义时（例如丢掉输出），也必须登记，不允许悄悄改变语义。
4. **不变量出错时直接报错。** 应该成立的事情用 `expect` 表达，不用默认值兜底（例如编一个名字、填 `undefined`、取第 0 个）。
5. **标准库按实现翻译，模型只是暂时的替代。** 用等价模型代替标准库的类型或函数时，必须登记在 `STD_MODELS.md` 中；没有模型的条目按外部类型或外部函数生成模板，不自行替换。手写的模型放在 AutoCorrode 的 `Micro_Rust_Std_Lib/StdLib_Frontend_Models.thy`。
6. **语言特性的处理登记在 `LANGUAGE_FEATURES.md` 中。** 它记录每类 Rust 语言构造翻译成什么（包括用其他表示替换 Rust 语义的地方）、哪些构造输出占位符。改变对某个构造的处理时，同步修改它。
7. **代码说明意图。** 不留无用代码和无用参数，不用 `let _ = …` 或 `#[allow(...)]` 压警告。不新增 README、CHANGELOG 或"修复说明"之类的文档，除非用户明确要求。

## 验证

- 本应保持行为不变的修改：用修改前后的两个前端分别翻译 `tests/crates` 中的全部 crate，逐个比较输出。每一处差异都要能对应到某一条修改。
- Isabelle 必须在内存上限下运行（`systemd-run --user --scope -p MemoryMax=… -p MemorySwapMax=0`）。运行前先和用户约定内存预算；本机内存不到 14 GB，曾经因此 OOM。
- 汇报时如实区分"已核对（依据是什么）"和"未验证"。"Isabelle 接受"只说明生成的 theory 良构，不说明翻译正确。
