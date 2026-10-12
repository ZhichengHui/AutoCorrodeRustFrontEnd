//! Identifier sanitation for Isabelle/HOL and uRust.
//!
//! Isabelle identifiers are `letter (letter | digit | _ | ')*`. Qualified Rust
//! names are flattened into a single identifier by joining the path segments
//! with `_` (dotted names are rejected by Isabelle as "Bad name binding").

/// Words that cannot be used as variable names inside a uRust program
/// (uRust grammar tokens, HOL inner-syntax keywords) or that name common HOL
/// constants (a constant name in a `case` pattern is not a binder).
const RESERVED: &[&str] = &[
    // uRust tokens
    "as", "break", "continue", "const", "else", "false", "for", "if", "in", "let", "loop",
    "match", "match_case", "match_switch", "mut", "return", "true", "unsafe", "while", "u8",
    "u16", "u32", "u64", "usize", "i8", "i16", "i32", "i64", "isize", "fuel", "panic",
    "unimplemented", "todo", "fatal", "assert", "assert_eq", "assert_ne", "debug_assert",
    "vec", "matches", "unreachable", "addr_of", "addr_of_mut", "log",
    // HOL inner syntax keywords
    "case", "of", "then", "O", "o", "div", "mod", "dvd", "fun", "SOME", "THE", "LEAST",
    "GREATEST", "op", "ALL", "EX", "UNIV", "WRT", "CONST", "TYPE", "PROP", "undefined",
    "default", "if", "let", "in", "where", "and", "is", "with", "sorry", "oops",
    // Frequently used HOL / AutoCorrode constants
    "id", "map", "min", "max", "fst", "snd", "length", "len", "rev", "filter", "sum", "count",
    "find", "cmp", "swap", "new", "take", "drop", "hd", "tl", "last", "butlast", "zip", "fold",
    "foldl", "foldr", "abs", "sgn", "gcd", "lcm", "set", "size", "nth", "upt", "concat",
    "insert", "remove", "push", "pop", "get", "put", "update", "contains", "is_empty", "range",
    "iter", "into_iter", "next", "ok", "err", "or", "and", "not", "xor", "inv", "pair", "list",
    "word", "nat", "int", "bool", "unit", "char", "string", "literal", "skip", "call", "bind",
    "sequence", "return_val", "return_func", "yield", "pause", "ref", "focus", "lens", "prism",
    "array", "vector", "result", "option", "Some", "None", "Ok", "Err", "the", "image",
    "split", "case_prod", "curry", "uncurry", "comp", "inj", "surj", "bij", "dom", "ran",
    "fresh", "assume", "obtain", "show", "have", "thus", "hence", "from", "using", "unfolding",
    "by", "proof", "qed", "done", "apply", "lemma", "theorem", "definition", "begin", "end",
    "x", "y", "z", "f", "g", "h", "P", "Q", "R", "s", "t", "e",
    "self_ref", "store_update", "deref", "funcall", "lift_fun", "FunctionBody", "Abort",
    "Success", "Return", "Yield", "Panic", "LoopReturn", "LoopBreak", "LoopContinue",
    "tnil", "TNil", "make", "mk", "map_option", "map_result", "is_some", "is_none", "is_ok",
    "is_err", "unwrap", "expect", "clone", "fold_left",
];

/// Single-letter / short names above are not dangerous as plain lambda binders, but
/// they are dangerous as case-pattern binders only if they are constants. We keep the
/// list conservative but do not rename one-letter variables: those are never HOL constants.
const SAFE_SHORT: &[&str] = &["x", "y", "z", "f", "g", "h", "P", "Q", "R", "s", "t", "e"];

fn is_reserved(s: &str) -> bool {
    RESERVED.contains(&s) && !SAFE_SHORT.contains(&s)
}

/// Turn an arbitrary string into an ASCII Isabelle identifier body.
pub fn ident_chars(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            out.push(c);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push('v');
    }
    // must start with a letter
    let first = out.chars().next().unwrap();
    if !first.is_ascii_alphabetic() {
        out = format!("v{}", out);
    }
    out
}

/// Name of a local variable / parameter.
pub fn local_name(s: &str) -> String {
    let base = ident_chars(s);
    if is_reserved(&base) { format!("{}_v", base) } else { base }
}

/// Name of a top-level HOL constant derived from Rust path segments.
pub fn global_name(segments: &[String]) -> String {
    let joined: Vec<String> = segments.iter().map(|s| ident_chars(s)).collect();
    let base = joined.join("_");
    if is_reserved(&base) { format!("{}_fn", base) } else { base }
}

/// HOL type names that must not be redefined.
const RESERVED_TYPES: &[&str] = &[
    "list", "option", "result", "unit", "bool", "nat", "int", "word", "sword", "char",
    "string", "set", "ref", "range", "ordering", "array", "vector", "iterator", "tnil",
    "prism", "lens", "focus", "expression", "function_body", "prompt", "prompt_output",
    "assert", "share", "literal", "gref", "focused", "num", "real", "rat", "integer",
    "prod", "sum", "fun", "itself", "loop_signal", "continuation", "log_data", "Result",
    "Option", "Vec", "String",
];

pub fn type_name(segments: &[String]) -> String {
    let base = global_name_raw(segments);
    if RESERVED_TYPES.contains(&base.as_str()) { format!("{}_t", base) } else { base }
}

fn global_name_raw(segments: &[String]) -> String {
    let joined: Vec<String> = segments.iter().map(|s| ident_chars(s)).collect();
    joined.join("_")
}

/// Type variable name for a Rust generic parameter. Locale type variables
/// ('s, 'addr, 'gv, 'abort, 'i, 'o) are lower-case; Rust type parameters are
/// conventionally upper-case, but we prefix them anyway to be safe.
pub fn tvar_name(s: &str) -> String {
    format!("'r{}", ident_chars(s))
}

/// Make a string safe to put inside a uRust string token `"..."`.
pub fn string_token(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        if c.is_ascii_alphanumeric() || " _:.,()<>=+-*/&|!?[]#@%^~;{}".contains(c) {
            out.push(c);
        } else if c == '\n' || c == '\t' {
            out.push(' ');
        } else {
            out.push('_');
        }
    }
    let mut out: String = out.split_whitespace().collect::<Vec<_>>().join(" ");
    if out.len() > 100 {
        out.truncate(100);
        out.push_str("...");
    }
    out
}

/// Is the string printable inside an Isabelle `''...''` string literal?
pub fn hol_string_ok(s: &str) -> bool {
    s.chars().all(|c| c.is_ascii() && !c.is_ascii_control() && c != '\'' && c != '\\' && c != '"')
}
