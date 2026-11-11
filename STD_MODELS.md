# 标准库的等价模型

前端的目标是把 Rust 程序完全按照 Rust 的实现翻译成 uRust 函数：只有语言内建类型（整数等）使用 Isabelle 的模型，标准库（`core`、`alloc`、`std`）的类型和函数都应按它们的 Rust 源码翻译。目前前端还不能翻译标准库的源码，所以对一部分标准库条目使用**等价模型**作为暂时的替代。本文件登记所有这样的模型。新增、修改或删除模型时，必须同步修改本文件。

## 设计选择

- **模型只是暂时的替代。** 每个模型最终都应被按 Rust 源码翻译的定义取代。没有模型的标准库条目不做替代：类型按外部类型、函数按外部函数生成模板（`*_External_Template.thy`），由用户补充定义。
- **模型的三种来源。**
  1. AutoCorrode 已有的类型和函数（`Micro_Rust_Std_Lib`、`Shallow_Micro_Rust`）。
  2. 手写的模型：放在 AutoCorrode 的 `Micro_Rust_Std_Lib/StdLib_Frontend_Models.thy`（AutoCorrode 分支 `urust-frontend-std-models`），属于 `Micro_Rust_Std_Lib` 会话，由 `Micro_Rust_Std_Lib.thy` 导入，因而生成的每个 crate 都能使用。这个文件只放标准库函数的模型，不限于某一个类型。
  3. 前端直接生成的写法（例如恒等、`[]`），不对应任何 Isabelle 定义。
- **序列的表示。** `Vec<T>` 和切片 `[T]` 都表示为元素的列表 `T list`，`&mut` 引用指向这个列表。这与 AutoCorrode 对切片的表示（`StdLib_Slice.thy` 的 `slice_index`）一致。代价是 `Vec` 的容量、内存位置没有建模。AutoCorrode 另有一个长度受类型参数限定的 `('v, 'l) vector` 类型，目前没有使用。
- **未定义行为。** 模型若需要表示 Rust 中的未定义行为，以消息以 `undefined behaviour` 开头的 panic 中止，与 Rust 自身的 panic 区分开（目前没有模型用到）。
- **重载解引用。** 编译器插入的 `Deref::deref`/`DerefMut::deref_mut`（自动解引用）不翻译成函数调用：解引用前后的类型（去掉引用后）翻译成的 HOL 类型相同时，当作恒等，否则登记为占位符（`pv_adjusted`）。这条规则依赖上面的类型替换，按现有的类型映射，满足它的只有 `Vec` 到切片、`String` 到 `str`、`Box<T>` 到 `T` 三种，下面各组分别列出。
- **模型目前没有契约和证明**（手写模型只有定义）。

## 语言内建类型的模型

| Rust | 模型 | 与 Rust 的差别 |
|---|---|---|
| `u8`…`u64`、`usize` | `N word`（`usize` 为 `64 word`） | 假设 64 位平台；溢出按 debug 构建的语义 panic |
| `i8`…`i64`、`isize` | `N sword`（`'l signed word`，`isize` 为 `64 sword`） | 同上；运算由 AutoCorrode `Numeric_Types` 定义，溢出、除法、取余、移位、比较、取负均按 Rust 的 debug 语义 |
| `i128`、`u128`、`f32`、`f64` | 无模型：占位类型，登记为占位符 | |
| `bool` | `bool` | |
| `char` | HOL `char` | HOL `char` 只有 256 个值；非 ASCII 的字面量登记为占位符，其他来源的非 ASCII 字符无法表示 |
| `str` | `String.literal` | 只能表示 ASCII；非 ASCII 字面量登记为占位符 |
| `&T` | `T` | 引用的身份（地址）不保留 |
| `&mut T` | `('addr, 'gv, T) Global_Store.ref` | |
| `[T]` | `T list` | |
| `[T; N]` | `T list` | AutoCorrode 另有定长数组类型 `('a, 'l) array`，未使用 |
| 元组 | `(A × B × tnil)` | |
| `!` | `unit` | |
| 闭包 | HOL 函数 | 修改捕获变量的闭包登记为占位符 |

（`Frontend::ty`）

## 标准库条目的模型

按条目所属的类型或 trait 分组。"位置"指前端中做替换的函数。

### Option
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Option<T>` | HOL `T option` | Isabelle/HOL | `Frontend::ty` |
| `Some`、`None`（构造和匹配） | HOL `Some`、`None` | Isabelle/HOL | `ctor_call`、`unit_ctor`、模式翻译 |
| `unwrap`、`expect` | `option_unwrap`、`option_expect` | AutoCorrode `StdLib_Option` | `std_fn`/`std_call` |
| `is_some`、`is_none` | `urust_func_option_is_some`、`urust_func_option_is_none` | AutoCorrode `StdLib_Option` | 同上 |
| `ok_or` | `ok_or` | AutoCorrode `StdLib_Option` | 同上 |
| `take` | `take_mut_ref_option` | AutoCorrode `StdLib_Option` | 同上 |

### Result
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Result<T, E>` | `(T, E) result` | AutoCorrode | `Frontend::ty` |
| `Ok`、`Err`（构造和匹配） | `Ok`、`Err` | AutoCorrode | `ctor_call`、模式翻译 |
| `unwrap`、`expect` | `result_unwrap`、`result_expect` | AutoCorrode `StdLib_Result` | `std_fn`/`std_call` |
| `is_ok`、`is_err` | `urust_func_result_is_ok`、`urust_func_result_is_err` | AutoCorrode `StdLib_Result` | 同上 |
| `ok` | `ok` | AutoCorrode `StdLib_Result` | 同上 |
| `unwrap_or` | `result_unwrap_or` | AutoCorrode `StdLib_Result` | 同上 |

### Try（`?` 运算符）
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `?`（`Try` 在 `Option`、`Result` 上的实现） | uRust 的 `?`；错误类型不同时显式 `match` 并调用 `From::from` | AutoCorrode | `val_unadj` 的 `TryDesugar`、`try_error_conversion` |

### Vec 与切片
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Vec<T>` | `T list` | Isabelle/HOL | `Frontend::ty` |
| `Vec::new`、`Vec::with_capacity` | `[]` | 前端写法 | `std_call` |
| `Vec::len`、`<[T]>::len` | `len` | AutoCorrode `Range_Type.thy` | `std_fn`/`std_call` |
| `<[T]>::to_vec`、`into_vec` | 恒等 | 前端写法 | 同上 |
| `Vec::as_slice`、`Vec` 到切片的 `Deref` | 恒等 | 前端写法 | `std_call`、`pv_adjusted` |
| `v[i]`（`Index`/`IndexMut`） | uRust 的列表下标 | AutoCorrode | `pv_unadj` 的 `Index` |
| `<[T]>::iter()`（在 `for` 中） | 直接遍历列表 | AutoCorrode | `for_loop` |
| `<[T]>::iter_mut()`、`for` 遍历 `&mut` 序列 | `iter_mut` | AutoCorrode `StdLib_Iterators` | `for_loop` |
| `Vec::push` | `vec_push`：追加到末尾 | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `Vec::pop` | `vec_pop`：空时 `None`，否则去掉并返回最后一个元素 | 手写 | 同上 |
| `<[T]>::swap` | `slice_swap`：交换两个位置，越界时 panic | 手写 | 同上 |
| `vec![x; n]`（`alloc::vec::from_elem`） | `vec_from_elem`：`replicate n x` | 手写 | 同上 |
| 数组重复表达式 `[x; N]`（语言构造，`N` 已知） | `vec_from_elem(x, N)` | 手写 | `BodyTr::expr`（`ExprKind::Repeat`） |

丢掉的语义：容量（`with_capacity`、`reserve` 的效果、`capacity()`）和元素的内存位置。

### Box
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Box<T>` | `T` | 前端写法 | `Frontend::ty` |
| `Box::new`、`Box` 的 `Deref` | 恒等 | 前端写法 | `std_call`、`pv_adjusted` |

丢掉的语义：堆分配和地址。

### String
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `String` | `String.literal` | Isabelle | `Frontend::ty` |
| `String` 到 `str` 的 `Deref`、`String::as_str` | 恒等 | 前端写法 | `pv_adjusted`、`std_call` |

丢掉的语义：容量；非 ASCII 内容无法表示。

### Ordering 与比较
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Ordering` 及其变体 | `ordering` | AutoCorrode `StdLib_Ordering` | `Frontend::ty`、`unit_ctor` |
| `Ord::cmp`（操作数为有符号或无符号整数；AutoCorrode 的 `cmp` 只定义在 word 上，有符号时按有符号数比较） | `cmp` | AutoCorrode `StdLib_Ordering` | `std_call`（`hol_ordered`） |

`bool`、`str`、`String` 的 `Ord::cmp` 没有模型（AutoCorrode 的 `cmp` 不接受这些类型），生成外部函数模板。

### 相等（PartialEq）
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 标准库实现与派生实现的 `==`、`!=` | HOL `=`、`≠` | Isabelle/HOL | `binary`（`structural_eq`）、`std_call` |

丢掉的语义：字段类型有自定义（非结构）的 `PartialEq` 时，派生实现不是结构相等；外部类型（如 `HashMap`）的相等不由表示决定。

### Clone
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 标准库实现与派生实现的 `clone` | 恒等 | 前端写法 | `std_call` |

丢掉的语义：字段类型有自定义的 `clone` 时，派生实现不是恒等。

### 转换 trait
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `ToString::to_string`、`ToOwned::to_owned`、`From::from`、`Into::into`、`AsRef::as_ref`、`Borrow::borrow`（实参与结果的 HOL 类型相同时） | 恒等 | 前端写法 | `std_call` |

### Range
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Range<T>`、`RangeInclusive<T>` | `T range` | AutoCorrode `Range_Type` | `Frontend::ty` |
| `a..b`、`RangeInclusive::new` | uRust 的区间表达式 | AutoCorrode | `struct_expr`、`std_call` |
| `for` 遍历区间 | uRust 的 `for` 循环 | AutoCorrode | `for_loop` |

### 整数的方法
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 无符号和有符号整数的 `checked_add`、`checked_mul`、`saturating_sub`、`div_ceil` | 同名函数（有符号时按有符号数） | AutoCorrode `StdLib_Arithmetic` | `std_fn`/`std_call` |
| 有符号整数的 `wrapping_add_unsigned` | 同名函数 | AutoCorrode `StdLib_Arithmetic` | 同上 |

无符号整数的 `wrapping_add` 不再有模型：AutoCorrode 只剩有符号的 `wrapping_add_unsigned`，所以按外部函数生成模板。其他整数方法（`cast_signed`、`cast_unsigned`、`abs`、`signum`、`unsigned_abs`、`wrapping_sub` 等）没有模型，同样生成外部函数模板。

### panic 与进程终止
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 返回 `!` 的标准库函数（`panic!` 的展开、`unreachable!`、`process::exit`、`abort` 等） | uRust `panic!`，消息取第一个字符串字面量 | AutoCorrode | `panic_or_print` |
| `print!`、`println!` 等输出 | 丢弃，登记为占位符 | | `panic_or_print` |

丢掉的语义：`process::exit` 和 `abort` 不是 panic；panic 消息中的格式化参数。

### 格式化（`format!`、`write!`）
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `fmt::Formatter` | `fmt_Formatter`（输出缓冲区与 `FormattingOptions` 的 flags、width、precision） | AutoCorrode `StdLib_Fmt` | `Frontend::ty` |
| `fmt::Error` | `fmt_Error` | AutoCorrode `StdLib_Fmt` | `Frontend::ty`、`unit_ctor` |
| `alloc::fmt::format`（`format!`）、`Formatter` 上的 `write_fmt`（`write!(f, …)`） | 按 `core::fmt::write` 解释 `format_args!` 的展开：前端解码模板字节串，字面片段用 `fmt_write_str`/`fmt_write_char` 写出；每个占位符按它的选项新建一个 formatter，用 `rt::Argument` 构造函数所约束的格式化 trait 的 `fmt`（在参数类型上解析，引用和 `Box` 先剥去，因为它们的实现只转发给内容：本地实现直接调用，基本类型用下面的模型）写入，再把输出写到目标；每次写入（字面片段、格式化、写回输出）的错误都结束输出并作为结果，与 `fmt::write` 中的 `?` 相同，`format` 遇到错误时 panic；动态宽度或精度（`rt::Argument::from_usize`）大于 `u16::MAX` 时在构造参数时 panic；`rt::Argument::new_debug_noop` 不输出任何内容；格式化 trait 是 `rt::Argument` 构造函数的约束（`Frontend::fmt_traits`），其中 `Pointer` 对引用的实现打印地址，不剥去引用（没有模型） | 前端写法 + `StdLib_Fmt` | `fmt_call` |
| `Display`、`Debug`、`LowerHex`、`UpperHex`、`Octal`、`Binary` 的 `fmt`，用于无符号与有符号整数、`bool`、`char`、`str`、`String` | `fmt_<Trait>_<word|sword|bool|char|str>`，按 `core::fmt` 的实现移植（填充、对齐、宽度、精度、`+`、`#`、`0`、`x?`） | AutoCorrode `StdLib_Fmt` | `fmt_arg_call`、`std_call` |
| `Formatter` 的 `write_str`、`write_char`、`pad`、`pad_integral`、`alternate`、`sign_plus`、`sign_minus`、`sign_aware_zero_pad`、`width`、`precision`、`fill`；`fmt::Write::write_str`/`write_char`（在 `Formatter` 上） | `fmt_<方法名>` | AutoCorrode `StdLib_Fmt` | `std_fn`/`std_call` |

与 Rust 的差别：字符串是 `String.literal`，只能表示 ASCII，输出中出现非 ASCII 字符时模型中止；目标是 `fmt::Write` 的其他实现（例如 `String`、`io::Write`）时没有模型。没有模型（登记为占位符）：浮点数、指针等其他类型的格式化，派生的 `Debug`，泛型参数类型的值的格式化，作为值传递的 `fmt::Arguments`。

### 恒等形状的函数
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 形如 `fn<T>(T) -> T`、类型参数没有带方法的约束的标准库函数（`hint::must_use`、`convert::identity`、`hint::black_box`） | 恒等 | 前端写法 | `std_call`（`identity_shaped`） |

### 内存
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `mem::drop` | 丢弃这个值 | 前端写法 | `std_call` |
