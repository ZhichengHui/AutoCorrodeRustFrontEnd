# 标准库的等价模型

前端的目标是把 Rust 程序完全按照 Rust 的实现翻译成 uRust 函数：只有语言内建类型（整数等）使用 Isabelle 的模型，标准库（`core`、`alloc`、`std`）的类型和函数都应按它们的 Rust 源码翻译。目前前端还不能翻译标准库的源码，所以对一部分标准库条目使用**等价模型**作为暂时的替代。本文件登记所有这样的模型。新增、修改或删除模型时，必须同步修改本文件。

## 设计选择

- **模型只是暂时的替代。** 每个模型最终都应被按 Rust 源码翻译的定义取代。没有模型的标准库条目不做替代：类型按外部类型、函数按外部函数生成模板（`*_External_Template.thy`），由用户补充定义。
- **模型的三种来源。**
  1. AutoCorrode 已有的类型和函数（`Micro_Rust_Std_Lib`、`Shallow_Micro_Rust`）。
  2. 手写的模型：放在 AutoCorrode 的 `Micro_Rust_Std_Lib/StdLib_Frontend_Models.thy`（AutoCorrode 分支 `urust-frontend-std-models`），属于 `Micro_Rust_Std_Lib` 会话，由 `Micro_Rust_Std_Lib.thy` 导入，因而生成的每个 crate 都能使用。这个文件只放标准库函数的模型，不限于某一个类型。例外是 `Vec`：它的类型、模型和契约自成一体，放在同一会话的 `StdLib_Vec.thy`。
  3. 前端直接生成的写法（例如恒等、`[]`），不对应任何 Isabelle 定义。
- **序列的表示。** 切片 `[T]` 和数组表示为元素的列表 `T list`，`&mut` 引用指向这个列表，与 AutoCorrode 对切片的表示（`StdLib_Slice.thy` 的 `slice_index`）一致。`Vec<T>` 表示为 AutoCorrode `StdLib_Vec` 的 `T rvec`：元素的列表、容量和元素类型的布局（大小、对齐）。它有 `Vec` 的长度上界（`Layout::array` 的 `n * size <= isize::MAX - (align - 1)`，零大小元素的容量为 `usize::MAX`）和超出上界时的 `capacity overflow` panic；标准库没有规定的容量（扩容的增量，`with_capacity`、`reserve_exact`、`shrink_to(_fit)`、`clone` 的结果）是只知道上下界的未指定值。`Vec` 用作列表的地方（到切片的 `Deref`、下标、`for`）取它的元素：值取 `rvec_elems`，引用经 `rvec_elems_focus` 聚焦到元素。布局写在创建 `Vec` 的地方（`make_elem_layout size align`，取自 rustc 的 `layout_of`），因为 `&T`、`Box<T>` 与 `T` 的 HOL 类型相同而大小不同；元素类型含类型参数时布局未知，用 AutoCorrode 的未指定常量 `rvec_layout_of TYPE(..)`，它对每个 HOL 类型是一个值，证明不能用到它的任何性质。元素的内存位置没有建模（缓冲区不在 store 中，重新分配不可见），分配失败（Rust 中 abort）也没有建模。
- **未定义行为。** 模型若需要表示 Rust 中的未定义行为，以消息以 `undefined behaviour` 开头的 panic 中止，与 Rust 自身的 panic 区分开（目前没有模型用到）。
- **重载解引用。** 编译器插入的 `Deref::deref`/`DerefMut::deref_mut`（自动解引用）不翻译成函数调用：`Vec` 到切片取元素（见上）；其余解引用前后的类型（去掉引用后）翻译成的 HOL 类型相同时，当作恒等，否则登记为占位符（`pv_adjusted`）。按现有的类型映射，后者只有 `String` 到 `str`、`Box<T>` 到 `T` 两种，下面各组分别列出。
- **模型目前没有契约和证明**（手写模型只有定义）。

## 语言内建类型的模型

| Rust | 模型 | 与 Rust 的差别 |
|---|---|---|
| `u8`…`u64`、`usize` | `N word`（`usize` 为 `64 word`） | 假设 64 位平台；溢出按 debug 构建的语义 panic |
| `i8`…`i64`、`isize` | `N sword`（`'l signed word`，`isize` 为 `64 sword`） | 同上；运算由 AutoCorrode `Numeric_Types` 定义，溢出、除法、取余、移位、比较、取负均按 Rust 的 debug 语义 |
| `i128`、`u128` | `128 sword`、`128 word` | 同上 |
| `f32`、`f64` | 无模型：占位类型，登记为占位符 | |
| `bool` | `bool` | |
| `char` | `32 word`：码点（AutoCorrode `StdLib_Utf8`） | 值总是 Unicode 标量值（`is_scalar`），这是产生字符的途径（字面量、`u8 as char`、`char::from_u32` 等的检查）保证的不变量，不由类型保证；与 `u32` 的 HOL 类型相同 |
| `str` | `8 word list`：UTF-8 编码的字节（写法与 `[u8]` 相同） | 值总是有效的 UTF-8（`utf8_valid`），同样是产生字符串的途径（字面量、`from_utf8` 的检查、模型）保证的不变量；`from_utf8_unchecked` 不检查，与 Rust 一样由调用者保证 |
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
| `unwrap_or`、`unwrap_or_else`、`map`、`and_then`、`ok_or_else` | `option_unwrap_or`、`option_unwrap_or_else`、`option_map`、`option_and_then`、`option_ok_or_else`：闭包在 Rust 调用它的位置调用 | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `copied`、`cloned`、`as_ref` | 恒等（`&T` 与 `T` 的 HOL 类型相同） | 前端写法 | 同上 |
| `is_some_and` | `option_is_some_and` | 手写 | 同上 |

### Result
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Result<T, E>` | `(T, E) result` | AutoCorrode | `Frontend::ty` |
| `Ok`、`Err`（构造和匹配） | `Ok`、`Err` | AutoCorrode | `ctor_call`、模式翻译 |
| `unwrap`、`expect` | `result_unwrap`、`result_expect` | AutoCorrode `StdLib_Result` | `std_fn`/`std_call` |
| `is_ok`、`is_err` | `urust_func_result_is_ok`、`urust_func_result_is_err` | AutoCorrode `StdLib_Result` | 同上 |
| `ok` | `ok` | AutoCorrode `StdLib_Result` | 同上 |
| `unwrap_or` | `result_unwrap_or` | AutoCorrode `StdLib_Result` | 同上 |
| `map`、`map_err` | `result_map`、`result_map_err` | 手写 `StdLib_Frontend_Models` | 同上 |

### Try（`?` 运算符）
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `?`（`Try` 在 `Option`、`Result` 上的实现） | uRust 的 `?`；错误类型不同时显式 `match` 并调用 `From::from` | AutoCorrode | `val_unadj` 的 `TryDesugar`、`try_error_conversion` |

### Vec 与切片
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Vec<T>` | `T rvec`（见“序列的表示”） | 手写 `StdLib_Vec` | `Frontend::ty` |
| `Vec` 到切片的 `Deref`/`DerefMut`、`*v`、`Vec::as_slice`、`Vec::into_boxed_slice`、`v[i]` 与 `for` 中的 `Vec` | 值的 `rvec_elems`，引用经 `rvec_elems_focus` 聚焦 | 手写 `StdLib_Vec` | `pv_adjusted`、`pv_unadj`（`index_seq`）、`for_loop`、`std_call` |
| `Vec::new`、`Vec::with_capacity(n)`、`Default::default()` | `rvec_new`、`rvec_with_capacity`（`n` 超出上界时 panic，容量未指定、不小于 `n`），布局为元素类型的布局，结果标注 HOL 类型 | 手写 `StdLib_Vec` | `std_call`、`default_value` |
| `vec![x; n]`（`alloc::vec::from_elem`） | `rvec_from_elem`：`n` 个 `x`，容量同 `with_capacity(n)` | 手写 `StdLib_Vec` | `std_call` |
| `<[T]>::into_vec`（`Box<[T]>` 到 `Vec`）、`From<[T; N]>` | `rvec_from_list`：容量为元素个数 | 手写 `StdLib_Vec` | `std_call`、`vec_conversion` |
| `<[T]>::to_vec`、`From<&[T]>`、`ToOwned::to_owned`（切片）、`collect`（到 `Vec`）、`String::into_bytes`、`FromUtf8Error::into_bytes` | `rvec_of_list_alloc`：新分配，容量未指定、不小于长度；元素过多时 panic。`into_bytes` 的容量在 Rust 中是字符串的容量，字符串的模型没有容量 | 手写 `StdLib_Vec` | 同上 |
| `IntoIterator::into_iter`（`Vec`、`&Vec` 到 `vec::IntoIter`、`slice::Iter`）、其他从 `Vec` 到其元素列表的同 HOL 类型转换 | `rvec_elems` | 手写 `StdLib_Vec` | `vec_conversion` |
| `Clone::clone`、`ToOwned::to_owned`（`Vec`） | `rvec_clone`：新分配，元素相同，容量未指定、不小于长度 | 手写 `StdLib_Vec` | `std_call`、`model_field` |
| `PartialEq`（`==`、`!=`）：元素不含 `Vec`、`HashMap` 的 `Vec` | `rvec_eq`、`rvec_ne`：比较元素，不比较容量 | 手写 `StdLib_Vec` | `std_call`、`model_field` |
| `Vec::len`、`capacity`、`is_empty`；`<[T]>::len` | `rvec_len`、`rvec_capacity`、`rvec_is_empty`；uRust 的 `len` | 手写 `StdLib_Vec`；AutoCorrode `Range_Type.thy` | `std_fn`/`std_call` |
| `Vec::push`、`extend_from_slice`、`reserve`、`reserve_exact`、`resize` | `rvec_push`、`rvec_extend_from_slice`、`rvec_reserve`、`rvec_reserve_exact`、`rvec_resize`：容量不够时扩容，新容量未指定（`reserve_exact` 不小于所需；其余在所需与 `max(2 * cap, 所需, MIN_NON_ZERO_CAP)` 之间），超出上界时 panic `capacity overflow` | 手写 `StdLib_Vec` | 同上 |
| `Vec::insert` | `rvec_insert`：下标大于长度时 panic，满时扩容 | 手写 `StdLib_Vec` | 同上 |
| `Vec::pop`、`remove`、`swap_remove`、`truncate`、`clear`、`dedup`（元素的 `PartialEq` 是结构相等，见下） | `rvec_pop`、`rvec_remove`、`rvec_swap_remove`（越界时 panic）、`rvec_truncate`、`rvec_clear`、`rvec_dedup`：容量不变 | 手写 `StdLib_Vec` | 同上 |
| `Vec::shrink_to_fit`、`shrink_to` | `rvec_shrink_to_fit`、`rvec_shrink_to`：容量减到目标与当前容量之间的未指定值；零大小元素的容量不变 | 手写 `StdLib_Vec` | 同上 |
| `Vec::as_mut_slice` | `rvec_as_mut_slice`：经 `rvec_elems_focus` 聚焦的引用 | 手写 `StdLib_Vec` | 同上 |
| `TryFrom<Vec<T>>`（及 `TryInto`）到 `[T; N]`、`Box<[T; N]>` | `rvec_try_into_array`：长度为 `N` 时 `Ok`（元素），否则 `Err` 为原值 | 手写 `StdLib_Vec` | 同上 |
| `TryFrom<Box<[T]>>`（及 `TryInto`）到 `[T; N]`、`Box<[T; N]>` | `vec_try_into_array`：长度为 `N` 时 `Ok`，否则 `Err` 为原值 | 手写 | 同上 |
| `v[i]`（`Index`/`IndexMut`，`v` 是切片、数组或 `Vec` 的元素） | uRust 的列表下标 | AutoCorrode | `pv_unadj` 的 `Index` |
| `<[T]>::iter()`（在 `for` 中） | 直接遍历列表 | AutoCorrode | `for_loop` |
| `<[T]>::iter_mut()`、`for` 遍历 `&mut` 序列 | `iter_mut` | AutoCorrode `StdLib_Iterators` | `for_loop` |
| `<[T]>::is_empty`、`first`、`last` | `slice_is_empty`、`slice_first`、`slice_last` | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `<[T]>::get(i)`（下标是 `usize`） | `slice_get`：越界时 `None` | 手写 | 同上 |
| `<[T]>::get(r)`（`r` 是 `a..b`、`a..=b`、`..b`、`..=b`、`a..`、`..`） | `slice_get_range`（`range` 值）、`slice_get_to`、`slice_get_to_inclusive`、`slice_get_from`、`slice_get_full`（后四者的参数是区间唯一的字段或 `()`）：区间递减或超出切片时 `None`（`a..=usize::MAX` 也是 `None`） | 手写 | 同上 |
| `<[T]>::copy_within(src, dest)`（`src` 是 `Range`、`RangeInclusive`） | `slice_copy_within`：复制 `src` 的元素到 `dest`（可以重叠）；`src` 递减、越界或目标越界时 panic | 手写 | 同上 |
| `TryFrom<&[T]>`（及 `TryInto`）到 `[T; N]`、`&[T; N]` | `slice_try_into_array`：长度为 `N` 时 `Ok`，否则 `Err(TryFromSliceError)`；`core::array::TryFromSliceError` 为 `try_from_slice_error`。从 `&mut [T]`、到 `&mut [T; N]` 的转换没有模型（结果与切片别名） | 手写 | 同上 |
| `<[T]>::sort`（`T` 的 `Ord` 是整数、`bool`、`char` 的序，或派生的、字段都满足此条件的本地结构体的字典序） | `slice_sort_by`，比较函数由前端按类型给出（`ord_cmp`、`ordering_then`）：稳定插入排序，与 Rust 的稳定排序结果相同 | 手写 + 前端写法 | `ord_cmp_term` |
| `<[T]>::chunks(n)` | `slice_chunks`：`n` 为 0 时 panic；状态见“迭代器” | 手写 | 同上 |
| `<[T]>::chunks_exact(n)` | `slice_chunks_exact`：`n` 为 0 时 panic；状态见“迭代器” | 手写 | 同上 |
| `<[T]>::copy_from_slice`、`fill`、`reverse` | `slice_copy_from_slice`（长度不等时 panic）、`slice_fill`、`slice_reverse` | 手写 | 同上 |
| 可变位置（`&mut`、赋值的左边、可变的自动借用）中的子切片 `v[r]`（`r` 是 `a..b`、`a..=b`、`a..`、`..b`、`..=b`、`..` 或存放区间的变量），以及读取时基有副作用的开区间、存放在变量中的区间 | `slice_range_mut`（`range` 值）、`slice_range_from_mut`、`slice_range_to_mut`、`slice_range_to_inclusive_mut`（区间唯一的字段）：指向子切片的引用，即 `v` 的引用经 `sublist_focus a k` 聚焦到前 `a` 个、后 `k` 个元素之间的部分；区间递减或超出切片时 panic；`..` 是 `v` 的引用本身。这个 focus 满足 AutoCorrode 对 focus 的全部定律（固定位置 `a..b` 的 focus 不满足，见 AutoCorrode `StdLib_Slice` 中注释掉的 `slice_index_range`）；借用存活期间切片的长度不变，所以它总是聚焦在区间 `r` 的元素上，与 Rust 一致 | 手写 `StdLib_Frontend_Models` | `pv_unadj` 的 `Index`（`index_place`）、`mark_mut_place` |
| `<[T]>::get_mut(i)`（下标是 `usize`）、`get_mut(r)`（`r` 是 `a..b`、`a..=b`） | `slice_get_mut`（`focus_nth` 的引用）、`slice_get_range_mut`（`sublist_focus` 的引用）：越界时 `None` | 手写 | `std_fn`/`std_call` |
| `<[T]>::iter_mut()` 作为值 | `slice_iter_mut_list`：各元素的引用的列表（`slice::IterMut` 的状态，见“迭代器”） | 手写 | 同上 |
| `<[T]>::swap` | `slice_swap`：交换两个位置，越界时 panic | 手写 | 同上 |
| 数组重复表达式 `[x; N]`（语言构造，`N` 已知） | `vec_from_elem(x, N)`（`replicate N x`，一个列表） | 手写 | `BodyTr::expr`（`ExprKind::Repeat`） |

丢掉的语义：元素的内存位置（重新分配不可见）和分配失败。未指定的容量是元素个数（或所需容量）与布局的一个确定的函数：同样的参数总得到同样的容量。含 `Vec` 的其他类型（`Option<Vec<T>>`、含 `Vec` 字段的本地类型）的 `clone` 仍是恒等（见“Clone”），所以其中 `Vec` 的容量不变，而 Rust 的克隆容量通常等于长度；它们的 `PartialEq` 不是 HOL 的相等（会比较容量），因此不再译成 `==`，而是外部函数模板。

### Box
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Box<T>` | `T` | 前端写法 | `Frontend::ty` |
| `Box::new`、`Box` 的 `Deref` | 恒等 | 前端写法 | `std_call`、`pv_adjusted` |

丢掉的语义：堆分配和地址。

### String
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `String` | `8 word list`（同 `str`） | 前端写法 | `Frontend::ty` |
| `String` 到 `str` 的 `Deref`、`String::as_str`；`as_bytes`、`into_bytes`、`into_boxed_str`、`from_utf8_unchecked`；`str` 到 `String` 的 `to_string`、`to_owned`、`From` | 恒等（实参与结果的 HOL 类型相同） | 前端写法 | `pv_adjusted`、`std_call` |
| `String::new`、`with_capacity` | `[]`（同 `Vec`：`with_capacity` 的实参不求值，容量超过 `isize::MAX` 时 Rust 的 panic 没有模型） | 前端写法 | `std_call` |
| `len`、`is_empty`（`String` 和 `str`） | uRust `len`、`slice_is_empty`（字节数） | AutoCorrode、手写 | `std_fn`/`std_call` |
| `push_str`、`String += &str` | `vec_extend_from_slice`（追加字节） | 手写 | 同上 |
| `push`、`pop`、`truncate`、`clear` | `string_push`（追加编码）、`string_pop`（去掉最后一个字符的编码）、`string_truncate`（新长度不在字符边界上时 panic）、`vec_clear` | 手写 | 同上 |
| `String + &str` | `string_add`（拼接） | 手写 | `std_fn`（`Add` 的 lang item）/`std_call` |
| `String::from_utf8` | `string_from_utf8`：有效时 `Ok` 字节，否则 `Err` 为 `from_utf8_error`（字节和 `utf8_error`）；`FromUtf8Error` 的 `utf8_error`、`into_bytes`、`as_bytes` | 手写 | 同上 |
| `char` 到 `String` 的 `to_string`、`From` | `char_to_string`（编码） | 手写 | `std_call` |
| 整数、`bool` 等有 `Display` 模型的类型（见“格式化”）的 `ToString::to_string` | `fmt_to_string`：以默认选项（`FormattingOptions::new()`）算出的 `Display` 文本，编码成 UTF-8，与 Rust 的 `ToString` 的一般实现相同 | AutoCorrode `StdLib_Fmt` | `std_call` |

丢掉的语义：容量。

### Ordering 与比较
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Ordering` 及其变体 | `ordering` | AutoCorrode `StdLib_Ordering` | `Frontend::ty`、`unit_ctor` |
| `Ord::cmp`（操作数为有符号或无符号整数；AutoCorrode 的 `cmp` 只定义在 word 上，有符号时按有符号数比较） | `cmp` | AutoCorrode `StdLib_Ordering` | `std_call`（`hol_ordered`）；标准库实现的字典字段（`model_field`） |

| `char` 的 `Ord::cmp` | `cmp`（按码点） | AutoCorrode `StdLib_Ordering` | `std_call`（`hol_ordered`） |
| `str`、`String` 的 `Ord::cmp` | `str_cmp`：字节的字典序（`bytes_cmp`），即字符的字典序 | 手写 | `std_call` |

`bool` 的 `Ord::cmp` 没有模型（AutoCorrode 的 `cmp` 不接受这个类型），生成外部函数模板。

字典（见 `LANGUAGE_FEATURES.md` 的“泛型与 trait”）中，标准库对同一种有模型的整数实现的 `Add`、`Sub`、`Mul`、`Div`、`Rem`、`BitAnd`、`BitOr`、`BitXor` 的方法和 `PartialOrd` 的 `lt`、`le`、`gt`、`ge` 是 uRust 的相应运算，`bool` 的 `BitAnd`、`BitOr`、`BitXor` 是 `&&`、`||`、`!=`，`char` 的 `Ord::cmp` 和 `PartialOrd` 的 `lt`、`le`、`gt`、`ge` 是码点上的 `cmp` 和比较，与直接写出的运算符的翻译（`binary`）相同（`model_field`）；移位和其他方法生成外部函数模板。

### 相等（PartialEq）
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 标准库实现与派生实现的 `==`、`!=` | HOL `=`、`≠` | Isabelle/HOL | `binary`（`structural_eq`）、`std_call`；标准库、派生和内建实现的字典字段（`model_field`） |

丢掉的语义：字段类型有自定义（非结构）的 `PartialEq` 时，派生实现不是结构相等；外部类型（如 `HashMap`）的相等不由表示决定。

### Clone
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 标准库实现与派生实现的 `clone`（`Vec` 的见“Vec 与切片”） | 恒等 | 前端写法 | `std_call`；标准库、派生和内建实现的字典字段（`model_field`，`clone_from` 为赋值） |

丢掉的语义：字段类型有自定义的 `clone` 时，派生实现不是恒等；含 `Vec` 的类型的克隆中 `Vec` 的容量不变。

### 转换 trait
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `ToString::to_string`、`ToOwned::to_owned`、`From::from`、`Into::into`、`AsRef::as_ref`、`Borrow::borrow`、`IntoIterator::into_iter`（实参与结果的 HOL 类型相同时，例如迭代器本身、切片的引用到 `slice::Iter`） | 恒等 | 前端写法 | `std_call` |
| 整数之间、`bool` 到整数的 `From::from`、`Into::into`（标准库只为无损的转换实现它们） | 与 `as` 相同的转换 | 前端写法 | `std_call` |

### Range
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `Range<T>`、`RangeInclusive<T>` | `T range` | AutoCorrode `Range_Type` | `Frontend::ty` |
| `a..b`、`RangeInclusive::new` | uRust 的区间表达式 | AutoCorrode | `struct_expr`、`std_call` |
| 整数区间的 `contains(&x)`（`Range`、`RangeInclusive`） | `contains` | AutoCorrode `StdLib_Range` | `std_fn`/`std_call` |
| `for` 遍历区间 | uRust 的 `for` 循环 | AutoCorrode | `for_loop` |
| `Range` 的字段 `start`、`end`（读取） | `range` 记录的选择函数 | AutoCorrode `Range_Type` | `pv_unadj` 的 `Field` |
| `RangeFrom<T>`、`RangeTo<T>`、`RangeToInclusive<T>`（`a..`、`..b`、`..=b` 的值）；`RangeFull`（`..`） | 唯一的字段（类型 `T`）；`unit` | 前端写法 | `Frontend::ty`、`struct_expr`、`unit_ctor`、`pv_unadj` 的 `Field` |

### 整数的方法
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 无符号和有符号整数的 `checked_add`、`checked_mul`、`saturating_sub`、`div_ceil` | 同名函数（有符号时按有符号数） | AutoCorrode `StdLib_Arithmetic` | `std_fn`/`std_call` |
| 有符号整数的 `wrapping_add_unsigned` | 同名函数 | AutoCorrode `StdLib_Arithmetic` | 同上 |
| 无符号和有符号整数的 `wrapping_add`、`wrapping_sub`、`wrapping_mul`、`trailing_zeros`、`leading_zeros`（按位的运算，与符号无关） | 同名函数（HOL word 的运算、`word_ctz`、`word_clz`） | 手写 `StdLib_Frontend_Models` | 同上 |
| `from_be_bytes`、`from_le_bytes`、`to_be_bytes`、`to_le_bytes`；`from_ne_bytes`、`to_ne_bytes` 按小端；`to_le` 为恒等 | `from_be_bytes`（结果标注类型）等，`word_rcat`、`word_rsplit` | 手写 | 同上 |
| 无符号整数的 `checked_sub`、`overflowing_sub`、`checked_shl` | 同名函数 | 手写 | 同上 |
| 无符号整数的 `Ord::min`、`Ord::max`、`cmp::min`、`cmp::max` | `ord_min`、`ord_max`（相等时 `min` 取第一个、`max` 取第二个，与 Rust 相同） | 手写 | 同上 |
| `mem::size_of::<T>()`（`T` 不含类型参数） | 由编译器给出的布局的字节数 | 前端写法 | 同上 |

平台假设：64 位、小端（`ne_bytes`）。有符号整数的 `checked_sub`、`overflowing_sub`、`min`、`max` 没有模型（HOL 中 word 的序是无符号的）。

### 迭代器

迭代器表示为它的状态；`next` 的模型是“步进函数”（AutoCorrode 的 `iter_step`：状态 ↦ 下一个元素（若有）和新状态），由前端按迭代器的类型组合（`Frontend::iter_step`）。数据源的状态是剩余的元素；适配器的状态是它的字段，第一个是内层迭代器的状态，与 Rust 的定义一致。适配器的 `next` 照 Rust 的实现调用内层的 `next`，所以带闭包的适配器也在 Rust 调用闭包的时刻调用。没有标准库的 lang 或 diagnostic item 的类型，由编译器确定为带 diagnostic item 的 trait 或类型的方法的结果类型（`std_adts_of`）。

| Rust | 状态（HOL 类型） | `next`（步进函数） | 来源 | 位置 |
|---|---|---|---|---|
| `slice::Iter<T>`（`<[T]>::iter`，以及 `&[T]`、`&Vec<T>` 的 `into_iter`） | `T list`（剩余元素；`T` 的引用与 `T` 的 HOL 类型相同） | `list_iter_next`；`next_back` 为 `list_iter_next_back` | 手写 `StdLib_Frontend_Models` | `Frontend::ty`、`iter_step` |
| `str::Lines`、`str::SplitWhitespace`、`str::Chars`、`str::CharIndices`、`str::Bytes` | 剩余的行、词（字节表的表）、字符（`32 word list`）、字符及其字节偏移（`(64 word × 32 word × tnil) list`）、字节（`8 word list`）；由 `str_lines` 等在创建时算出，`str` 不可变 | 同上 | 手写 | 同上 |
| `slice::ChunksExact<T>` | `T list list × T list × tnil`（剩余的块、余数） | `chunks_exact_next` | 手写 | 同上 |
| `Enumerate<I>` | `I × 64 word × tnil`（内层、计数） | `enumerate_next`：计数溢出时 panic | 手写 | 同上 |
| `Zip<A, B>` | `A × B × tnil` | `zip_next`：只在 `A` 有元素时推进 `B`（Rust 的一般实现） | 手写 | 同上 |
| `Skip<I>`、`Take<I>` | `I × 64 word × tnil` | `skip_next`（第一次 `next` 时用 `nth` 跳过）、`take_next` | 手写 | 同上 |
| `TakeWhile<I, P>` | `I × bool × P × tnil`（内层、已结束、谓词） | `take_while_next` | 手写 | 同上 |
| `Map<I, F>` | `I × F × tnil` | `map_next`（`next_back` 用内层的 `next_back`） | 手写 | 同上 |
| `Rev<I>`、`Copied<I>`、`Cloned<I>` | `I` | 内层的 `next_back`（`Rev`）、内层的 `next` | 手写 | 同上 |
| `Iterator::next(&mut it)` | `iter_ref_next(步进函数, it)`：读状态、步进、写回 | | 手写 | `iter_call` |
| `enumerate`、`zip`、`skip`、`take`、`take_while`、`map`、`rev`、`copied`、`cloned` | 构造适配器的状态（`zip` 的参数经 `IntoIterator`，HOL 类型相同时为恒等） | | 前端写法 | `iter_call` |
| `vec::IntoIter<T>`（`Vec` 按值的 `into_iter`） | `T list` | `list_iter_next`（`next_back` 同 `slice::Iter`） | 手写 | 同上 |
| `slice::Chunks<T>` | `T list × 64 word × tnil`（剩余元素、块大小） | `chunks_next`（最后一块可以较短） | 手写 | 同上 |
| `Filter<I, P>` | `I × P × tnil` | `filter_next`：内层的 `find`，带 crate 的燃料 | 手写 | 同上 |
| 无符号整数的 `a..b`、`a..=b`、`a..` 作为迭代器 | `range` 记录、下一个值 | `range_next`、`range_next_back`（耗尽的 `a..=b`，即 Rust 的 `exhausted`，表示为空的 `b+1..b+1`，即 Rust 以它作切片下标时取的区间；`b` 为最大值时为 `b..b`，切片同样短于它）、`range_from_next`（溢出时 panic） | 手写 | 同上 |
| `slice::IterMut<T>` | 剩余元素的引用的列表 | `list_iter_next`、`list_iter_next_back` | 手写 | 同上 |
| `for_each(f)` | `iter_for_each`：按顺序对每个元素调用 `f`（`iter_fold`，带 crate 的燃料） | | 手写 | `iter_call` |
| `any(&mut self, f)`、`min`（无符号整数） | `iter_ref_any`（写回迭代器的状态）、`iter_min`（第一个最小的元素） | | 手写 | `iter_call` |
| `count`、`collect`（到 `Vec`） | `iter_count`、`iter_collect_list`（`iter_fold`：用 crate 的 `urust_fuel` 逐个调用步进函数，燃料耗尽时 panic “out of fuel”，与递归函数相同；`count` 计数溢出时 panic） | | 手写 | `iter_call` |
| `for` 遍历上述迭代器 | Rust 的展开：`while let Some(p) = Iterator::next(&mut iter)` | | 前端写法 | `for_loop` |

丢掉的语义：`Zip` 在两边都可随机访问时的特化实现（只影响带副作用的内层迭代器被推进的次数，这里的数据源都没有副作用）。其他适配器、`collect` 到其他类型等没有模型，生成外部函数模板。

### HashMap

`HashMap<K, V, S>` 表示为键值对的列表 `(K × V × tnil) list`（键互不相同）。只为不暴露迭代顺序的方法提供模型，所以哈希和迭代顺序都观察不到；键用 HOL 的相等比较，只在 `K` 的 `PartialEq` 是结构相等时使用：整数、`bool`、`char`、`str`、`String`，它们的元组、数组、切片、`Option`，以及派生 `PartialEq` 且字段都满足此条件的本地类型（`structural_eq_ty`）。泛型代码中以含类型参数的键调用这些方法的函数按实例翻译（`GenericCalls`）。

| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `HashMap::new`、`len`、`is_empty`、`contains_key`、`get`、`insert`（已有键时替换值、保留键）、`remove` | `hashmap_new` 等 | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `get_mut`、`entry(k).or_insert(v)` | `hashmap_get_mut`、`hashmap_entry`、`hashmap_entry_or_insert`：引用由 `focus_nth` 和元组分量的透镜聚焦到值；`Entry` 表示为（表的引用、键） | 手写 | 同上 |

迭代（`iter`、`keys`、`values` 等）没有模型。

### 其他
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `c.encode_utf8(buf).as_bytes()` | `char_encode_utf8_bytes(c, buf)`：编码写入 `buf` 开头（太短时 panic），结果是编码的字节；中间的 `&mut str` 不出现 | 手写 | `encode_utf8_bytes` |
| 无符号整数的 `PartialOrd::partial_cmp` | `partial_cmp_word`：`Some` 比较结果 | 手写 | `std_call` |
| `Default::default()`：整数、`bool`、`char`、`Option`、`Vec`、`String`、这些类型的元组和数组，派生 `Default` 的本地结构体 | 各字段的默认值（`0`、`false`、`'\0'`、`None`、`[]`、`""`、构造子） | 前端写法 | `default_value` |
| 派生 `Eq` 的隐藏方法 `assert_receiver_is_total_eq`（字典字段） | 无操作 | 前端写法 | `model_field` |

### str
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
字符串是 UTF-8 字节的表，字符是码点（AutoCorrode `StdLib_Utf8` 的纯函数：编码 `char_utf8`、解码 `utf8_decode`、校验 `utf8_check`，按 `core` 的实现）。

| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `lines`、`split_whitespace`、`chars`、`char_indices`、`bytes` | `str_lines`（按 Rust 的实现：`split_inclusive('\n')`，去掉 `\n` 和其前的 `\r`，两者都不出现在多字节序列中）、`str_split_whitespace`（按 `char::is_whitespace`，即 Unicode `White_Space`）、`str_chars`（解码）、`str_char_indices`、恒等 | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `as_bytes` | `str_as_bytes`（恒等） | 手写 | 同上 |
| `trim`、`trim_start`、`trim_end` | `str_trim` 等（去掉首尾的 `is_whitespace` 字符） | 手写 | 同上 |
| `starts_with`、`ends_with`、`strip_prefix`、`strip_suffix`、`contains`、`find`（模式为 `char`、`&str` 或 `&String`） | `str_starts_with_char`、`str_starts_with_str` 等：在字节上比较（字符按其编码；有效 UTF-8 在有效 UTF-8 中的匹配总在字符边界上开始）；闭包、字符切片等其他模式没有模型 | 手写 | 同上 |
| `s[r]`（`r` 为各种区间）、`get(r)`、`split_at(i)`、`is_char_boundary(i)` | `str_index_range` 等、`str_get_range` 等、`str_split_at`：按字节位置，区间越界、递减或端点不在字符边界上时 panic（`get` 为 `None`），与 Rust 相同；panic 的消息不同 | 手写 | `str_index`、`std_call` |
| `repeat(n)` | `str_repeat`：长度溢出 `usize` 时 panic | 手写 | `std_fn`/`std_call` |
| `is_ascii`、`eq_ignore_ascii_case`、`to_ascii_uppercase`、`to_ascii_lowercase`（`str` 和 `[u8]`） | `bytes_is_ascii` 等 | 手写 | 同上 |
| `str::from_utf8`（函数和关联函数） | `str_from_utf8`：有效时 `Ok` 字节，否则 `Err` 为 `utf8_error`（`valid_up_to`、`error_len`，按 `run_utf8_validation` 算出）；`Utf8Error` 的 `valid_up_to`、`error_len` | 手写 | 同上 |
| `str::from_utf8_unchecked` | 恒等（不检查，由调用者保证有效） | 前端写法 | 同上 |
| `str::Utf8Error`、`string::FromUtf8Error` | `utf8_error`、`from_utf8_error`（由 `str::from_utf8`、`String::from_utf8` 的诊断项的结果类型确定） | 手写 | `Frontend::ty`、`std_adts_of` |
| `parse::<F>`（`F` 为整数类型）、整数的 `from_str_radix` | `str_parse_word`、`str_parse_sword`、`from_str_radix_word`、`from_str_radix_sword`：按 `from_ascii_bytes_radix`（基数不在 2 到 36 之间时 panic；可选的 `+`，有符号时可选的 `-`；数字按 `char::to_digit`；非数字先于溢出报错） | 手写 | 同上 |
| `num::ParseIntError` | `int_error_kind`（它唯一的字段 `IntErrorKind`） | 手写 | `Frontend::ty` |
| `Option::expect`、`Result::expect` 的消息 | `option_expect_str`、`result_expect_str`：消息（字节）转成 HOL 的 `String.literal` 作为 panic 消息，非 ASCII 字节写成 `?`（`str_message`；panic 消息不影响语义） | 手写 | `std_call` |

没有模型（生成外部函数模板）：其他 `str` 方法（例如 `split`、`replace`、`to_uppercase`、`to_lowercase`）。

### char
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `c as T`、`b as char`（`b: u8`）、`From<u8> for char`、`From<char> for u32/u64/u128` | 按 `u32` 的整数转换 | 前端写法 | `cast`、`std_call` |
| `char::MAX`、`char::REPLACEMENT_CHARACTER` 等常量 | 求值成字面量 | 前端写法 | `scalar_const` |
| `from_u32` | `char_from_u32`：标量值时 `Some` | 手写 | `std_fn`/`std_call` |
| `len_utf8`、`to_digit`、`from_digit` | `char_len_utf8`、`char_to_digit`、`char_from_digit`（基数不合法时 panic，与 Rust 相同） | 手写 | 同上 |
| `is_whitespace`、`is_control` | `char_is_whitespace_fn`（Unicode `White_Space`）、`char_is_control_fn`（`Cc`：0–0x1F、0x7F–0x9F） | 手写 | 同上 |
| `u8` 和 `char` 的 `is_ascii`、`is_ascii_alphabetic` 等 ASCII 类别、`to_ascii_uppercase`、`to_ascii_lowercase`、`eq_ignore_ascii_case` | `ascii_test`（类别是 `StdLib_Utf8` 中码值上的谓词）、`ascii_to_uppercase` 等 | 手写 | 同上 |

需要 Unicode 数据表的方法（`is_alphabetic`、`is_alphanumeric`、`is_numeric`、`is_lowercase`、`is_uppercase`、`to_uppercase`、`to_lowercase`）没有模型，生成外部函数模板。

其他整数方法（`cast_signed`、`cast_unsigned`、`abs`、`signum`、`unsigned_abs` 等）没有模型，生成外部函数模板。

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
| `alloc::fmt::format`（`format!`）、`Formatter` 上的 `write_fmt`（`write!(f, …)`） | 按 `core::fmt::write` 解释 `format_args!` 的展开：前端解码模板字节串，字面片段用 `fmt_write_str` 写出；每个占位符按它的选项新建一个 formatter，用 `rt::Argument` 构造函数所约束的格式化 trait 的 `fmt`（在参数类型上解析，引用和 `Box` 先剥去，因为它们的实现只转发给内容：本地实现直接调用，基本类型用下面的模型）写入，再把输出写到目标；每次写入（字面片段、格式化、写回输出）的错误都结束输出并作为结果，与 `fmt::write` 中的 `?` 相同，`format` 遇到错误时 panic；动态宽度或精度（`rt::Argument::from_usize`）大于 `u16::MAX` 时在构造参数时 panic；`rt::Argument::new_debug_noop` 不输出任何内容；格式化 trait 是 `rt::Argument` 构造函数的约束（`Frontend::fmt_traits`），其中 `Pointer` 对引用的实现打印地址，不剥去引用（没有模型） | 前端写法 + `StdLib_Fmt` | `fmt_call` |
| `Display`、`Debug`、`LowerHex`、`UpperHex`、`Octal`、`Binary` 的 `fmt`，用于无符号与有符号整数、`bool`、`char`、`str`、`String` | `fmt_<Trait>_<word|sword|bool|char|str>`，按 `core::fmt` 的实现移植（填充、对齐、宽度、精度、`+`、`#`、`0`、`x?`） | AutoCorrode `StdLib_Fmt` | `fmt_arg_call`、`std_call` |
| `Formatter` 的 `write_str`、`write_char`、`pad`、`pad_integral`、`alternate`、`sign_plus`、`sign_minus`、`sign_aware_zero_pad`、`width`、`precision`、`fill`；`fmt::Write::write_str`/`write_char`（在 `Formatter` 上） | `fmt_<方法名>` | AutoCorrode `StdLib_Fmt` | `std_fn`/`std_call` |

formatter 的输出是 Unicode 码点的列表：写入的字符串先解码，占位符的子 formatter 的输出用 `fmt_formatter_codes` 按码点写回，读成 `String`（`format!`）时再编码成 UTF-8。`Debug` 格式化含 U+0080 以上字符的字符串或字符时模型以 `Unimplemented` 中止（Rust 按 Unicode 属性决定是否转义，没有模型）。与 Rust 的差别：目标是 `fmt::Write` 的其他实现（例如 `String`、`io::Write`）时没有模型。没有模型（登记为占位符）：浮点数、指针等其他类型的格式化，派生的 `Debug`，泛型参数类型的值的格式化，作为值传递的 `fmt::Arguments`。

### 恒等形状的函数
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 形如 `fn<T>(T) -> T`、类型参数没有带方法的约束的标准库函数（`hint::must_use`、`convert::identity`、`hint::black_box`） | 恒等 | 前端写法 | `std_call`（`identity_shaped`） |

### 内存
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `mem::drop` | 丢弃这个值 | 前端写法 | `std_call` |
| `mem::swap(x, y)`、`mem::replace(dest, v)` | `mem_swap`、`mem_replace`（返回旧值） | 手写 | `std_fn`/`std_call` |
