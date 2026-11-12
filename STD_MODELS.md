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
| `i128`、`u128` | `128 sword`、`128 word` | 同上 |
| `f32`、`f64` | 无模型：占位类型，登记为占位符 | |
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
| `Vec<T>` | `T list` | Isabelle/HOL | `Frontend::ty` |
| `Vec::new`、`Vec::with_capacity` | `[]` | 前端写法 | `std_call` |
| `Vec::len`、`<[T]>::len` | `len` | AutoCorrode `Range_Type.thy` | `std_fn`/`std_call` |
| `<[T]>::to_vec`、`into_vec` | 恒等 | 前端写法 | 同上 |
| `Vec::as_slice`、`Vec` 到切片的 `Deref` | 恒等 | 前端写法 | `std_call`、`pv_adjusted` |
| `v[i]`（`Index`/`IndexMut`） | uRust 的列表下标 | AutoCorrode | `pv_unadj` 的 `Index` |
| `<[T]>::iter()`（在 `for` 中） | 直接遍历列表 | AutoCorrode | `for_loop` |
| `<[T]>::iter_mut()`、`for` 遍历 `&mut` 序列 | `iter_mut` | AutoCorrode `StdLib_Iterators` | `for_loop` |
| `<[T]>::is_empty`、`Vec::is_empty`、`first`、`last` | `slice_is_empty`、`slice_first`、`slice_last` | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `<[T]>::get(i)`（下标是 `usize`） | `slice_get`：越界时 `None` | 手写 | 同上 |
| `<[T]>::get(r)`（`r` 是 `a..b`、`a..=b`、`..b`、`..=b`、`a..`、`..`） | `slice_get_range`（`range` 值）、`slice_get_to`、`slice_get_to_inclusive`、`slice_get_from`、`slice_get_full`（后四者的参数是区间唯一的字段或 `()`）：区间递减或超出切片时 `None`（`a..=usize::MAX` 也是 `None`） | 手写 | 同上 |
| `<[T]>::copy_within(src, dest)`（`src` 是 `Range`、`RangeInclusive`） | `slice_copy_within`：复制 `src` 的元素到 `dest`（可以重叠）；`src` 递减、越界或目标越界时 panic | 手写 | 同上 |
| `TryFrom<&[T]>`（及 `TryInto`）到 `[T; N]`、`&[T; N]` | `slice_try_into_array`：长度为 `N` 时 `Ok`，否则 `Err(TryFromSliceError)`；`core::array::TryFromSliceError` 为 `try_from_slice_error`。从 `&mut [T]`、到 `&mut [T; N]` 的转换没有模型（结果与切片别名） | 手写 | 同上 |
| `TryFrom<Vec<T>>`、`TryFrom<Box<[T]>>`（及 `TryInto`）到 `[T; N]`、`Box<[T; N]>` | `vec_try_into_array`：长度为 `N` 时 `Ok`，否则 `Err` 为原值 | 手写 | 同上 |
| `Vec::shrink_to_fit` | `vec_shrink_to_fit`：无操作（只改变容量，模型没有容量） | 手写 | 同上 |
| `<[T]>::chunks_exact(n)` | `slice_chunks_exact`：`n` 为 0 时 panic；状态见“迭代器” | 手写 | 同上 |
| `<[T]>::copy_from_slice`、`fill`、`reverse` | `slice_copy_from_slice`（长度不等时 panic）、`slice_fill`、`slice_reverse` | 手写 | 同上 |
| `Vec::truncate`、`clear`、`resize`、`extend_from_slice` | `vec_truncate`、`vec_clear`、`vec_resize`、`vec_extend_from_slice` | 手写 | 同上 |
| `Vec::into_boxed_slice` | 恒等 | 前端写法 | 同上 |
| 作为调用参数（或方法的接收者）的 `&mut v[a..b]`（`a..b`、`a..`、`..b`、`..=b`、`..`）；`for` 遍历 `&mut v[a..b]`（循环体只能正常结束或跳出本循环） | 子切片复制到新的可变局部变量，引用它；调用（循环）之后用 `slice_splice` 写回 `v`。借用存活期间 Rust 不允许访问 `v`，切片的长度不变，所以与 Rust 一致。`let x = &mut v[a..b]`（及结果都是同一序列的子切片或整体借用的 `if`）在 `x` 最后一次使用之后写回（条件见 `LANGUAGE_FEATURES.md`）。调用可能保留借用时（结果带生命周期，或其他参数是指向带生命周期之物的引用、按值传入的带生命周期的值）、借用出现在其他位置时，仍是占位符 | 手写 `slice_splice` + 前端写法 | `borrow_mut`、`call_args`、`with_writeback`、`for_loop` |
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
| `Ord::cmp`（操作数为有符号或无符号整数；AutoCorrode 的 `cmp` 只定义在 word 上，有符号时按有符号数比较） | `cmp` | AutoCorrode `StdLib_Ordering` | `std_call`（`hol_ordered`）；标准库实现的字典字段（`model_field`） |

`bool`、`str`、`String` 的 `Ord::cmp` 没有模型（AutoCorrode 的 `cmp` 不接受这些类型），生成外部函数模板。

字典（见 `LANGUAGE_FEATURES.md` 的“泛型与 trait”）中，标准库对同一种有模型的整数实现的 `Add`、`Sub`、`Mul`、`Div`、`Rem`、`BitAnd`、`BitOr`、`BitXor` 的方法和 `PartialOrd` 的 `lt`、`le`、`gt`、`ge` 是 uRust 的相应运算，`bool` 的 `BitAnd`、`BitOr`、`BitXor` 是 `&&`、`||`、`!=`，与直接写出的运算符的翻译（`binary`）相同（`model_field`）；移位和其他方法生成外部函数模板。

### 相等（PartialEq）
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 标准库实现与派生实现的 `==`、`!=` | HOL `=`、`≠` | Isabelle/HOL | `binary`（`structural_eq`）、`std_call`；标准库、派生和内建实现的字典字段（`model_field`） |

丢掉的语义：字段类型有自定义（非结构）的 `PartialEq` 时，派生实现不是结构相等；外部类型（如 `HashMap`）的相等不由表示决定。

### Clone
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| 标准库实现与派生实现的 `clone` | 恒等 | 前端写法 | `std_call`；标准库、派生和内建实现的字典字段（`model_field`，`clone_from` 为赋值） |

丢掉的语义：字段类型有自定义的 `clone` 时，派生实现不是恒等。

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
| `str::Lines`、`str::SplitWhitespace`、`str::Chars` | `String.literal list`、`char list`（剩余的行、词、字符；由 `str_lines` 等在创建时算出，`str` 不可变） | 同上 | 手写 | 同上 |
| `slice::ChunksExact<T>` | `T list list × T list × tnil`（剩余的块、余数） | `chunks_exact_next` | 手写 | 同上 |
| `Enumerate<I>` | `I × 64 word × tnil`（内层、计数） | `enumerate_next`：计数溢出时 panic | 手写 | 同上 |
| `Zip<A, B>` | `A × B × tnil` | `zip_next`：只在 `A` 有元素时推进 `B`（Rust 的一般实现） | 手写 | 同上 |
| `Skip<I>`、`Take<I>` | `I × 64 word × tnil` | `skip_next`（第一次 `next` 时用 `nth` 跳过）、`take_next` | 手写 | 同上 |
| `TakeWhile<I, P>` | `I × bool × P × tnil`（内层、已结束、谓词） | `take_while_next` | 手写 | 同上 |
| `Map<I, F>` | `I × F × tnil` | `map_next`（`next_back` 用内层的 `next_back`） | 手写 | 同上 |
| `Rev<I>`、`Copied<I>`、`Cloned<I>` | `I` | 内层的 `next_back`（`Rev`）、内层的 `next` | 手写 | 同上 |
| `Iterator::next(&mut it)` | `iter_ref_next(步进函数, it)`：读状态、步进、写回 | | 手写 | `iter_call` |
| `enumerate`、`zip`、`skip`、`take`、`take_while`、`map`、`rev`、`copied`、`cloned` | 构造适配器的状态（`zip` 的参数经 `IntoIterator`，HOL 类型相同时为恒等） | | 前端写法 | `iter_call` |
| `count`、`collect`（到 `Vec`） | `iter_count`、`iter_collect_list`（`iter_fold`：用 crate 的 `urust_fuel` 逐个调用步进函数，燃料耗尽时 panic “out of fuel”，与递归函数相同；`count` 计数溢出时 panic） | | 手写 | `iter_call` |
| `for` 遍历上述迭代器 | Rust 的展开：`while let Some(p) = Iterator::next(&mut iter)` | | 前端写法 | `for_loop` |

丢掉的语义：`Zip` 在两边都可随机访问时的特化实现（只影响带副作用的内层迭代器被推进的次数，这里的数据源都没有副作用）。其他适配器、`collect` 到其他类型等没有模型，生成外部函数模板。

### str
| Rust | 模型 | 来源 | 位置 |
|---|---|---|---|
| `lines`、`split_whitespace`、`chars` | `str_lines`（按 Rust 的实现：`split_inclusive('\n')`，去掉 `\n` 和其前的 `\r`）、`str_split_whitespace`（ASCII 的 Unicode 空白：9–13、32）、`str_chars` | 手写 `StdLib_Frontend_Models` | `std_fn`/`std_call` |
| `as_bytes` | `str_as_bytes`（ASCII 字符的码值） | 手写 | 同上 |
| `starts_with`（模式为 `char` 或 `&str`） | `str_starts_with_char`、`str_starts_with_str` | 手写 | 同上 |
| `parse::<F>`（`F` 为整数类型） | `str_parse_word`、`str_parse_sword`：按 `from_str_radix(s, 10)`（可选的 `+`，有符号时可选的 `-`；非数字先于溢出报错） | 手写 | 同上 |
| `num::ParseIntError` | `int_error_kind`（它唯一的字段 `IntErrorKind`） | 手写 | `Frontend::ty` |

由于 `str` 是 `String.literal`（只有 ASCII），这些模型都只处理 ASCII 字符串，与 Rust 在 ASCII 字符串上的行为一致。

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
