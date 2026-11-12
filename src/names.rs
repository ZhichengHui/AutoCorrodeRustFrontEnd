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
    // HOL inner syntax keywords (including infix operators written as words)
    "case", "of", "then", "O", "o", "div", "mod", "dvd", "fun", "choose", "XOR", "AND", "OR",
    "NOT", "SUP", "INF", "Sup", "Inf", "Min", "Max", "Bex", "Ball", "Collect", "insert",
    "Let", "If", "Pair", "Suc", "BIT", "OFCLASS", "SORT_CONSTRAINT", "pred", "in_rel", "SOME", "THE", "LEAST",
    "GREATEST", "op", "ALL", "EX", "UNIV", "WRT", "CONST", "TYPE", "PROP", "undefined",
    // HOL binder notations (big operators), not usable as terms
    "MAX", "MIN", "SUM", "PROD", "SIGMA", "PI", "INT", "UN", "ARG_MIN", "ARG_MAX", "INFM", "MOST",
    // HOL literal syntax
    "STR", "CHR",
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
    "self_ref", "store_update", "deref", "funcall", "lift_fun", "FunctionBody", "Abort",
    "Success", "Return", "Yield", "Panic", "LoopReturn", "LoopBreak", "LoopContinue",
    "tnil", "TNil", "make", "mk", "map_option", "map_result", "is_some", "is_none", "is_ok",
    "is_err", "unwrap", "expect", "clone", "fold_left",
];

/// Isar outer-syntax keywords: not usable as names of `definition`s.
const OUTER_KEYWORDS: &[&str] = &[
    "record", "keywords", "imports", "theory", "begin", "end", "definition", "abbreviation", "lemma",
    "theorem", "corollary", "proposition", "fun", "function", "primrec", "datatype", "codatatype",
    "type_synonym", "typedecl", "locale", "context", "text", "txt", "section", "subsection",
    "chapter", "paragraph", "notation", "no_notation", "consts", "axiomatization", "instance",
    "instantiation", "class", "interpretation", "sublocale", "global_interpretation", "inductive",
    "coinductive", "termination", "value", "term", "thm", "typ", "prop", "export_code", "declare",
    "lemmas", "named_theorems", "method", "attribute", "syntax", "translations", "experiment",
    "bundle", "include", "including", "includes", "unbundle", "proof", "qed", "by", "apply", "done",
    "oops", "sorry", "using", "unfolding", "fix", "assume", "presume", "obtain", "show", "have",
    "thus", "hence", "then", "from", "with", "note", "moreover", "ultimately", "also", "finally",
    "next", "case", "where", "and", "for", "fixes", "assumes", "shows", "obtains", "defines",
    "notes", "constrains", "is", "if", "when", "open", "overloaded", "pervasive", "private",
    "qualified", "monos", "binder", "infix", "infixl", "infixr", "structure", "ML", "setup",
    "simproc_setup", "hide_const", "hide_type", "hide_fact", "adhoc_overloading", "nitpick",
    "quickcheck", "sledgehammer", "print_theorems", "find_theorems", "datatype_record",
    "scalable_datatype_record", "urust_const_data", "simple_word_enum", "enum",
    "micro_rust_record", "micro_rust_notation", "nonterminal", "parse_translation",
    "print_translation", "parse_ast_translation", "type_notation", "default_sort", "oracle",
    "partial_function", "nominal_function", "fun_cases", "inductive_set", "specification",
    "functor", "free_constructors", "lift_definition", "quotient_type", "typedef", "copy_bnf",
    "bnf", "old_datatype", "old_rep_datatype", "code_printing", "code_identifier", "schematic_goal",
    "supply", "guess", "let", "write", "back", "defer", "prefer", "subgoal", "unfolding",
];

fn is_reserved(s: &str) -> bool {
    RESERVED.contains(&s)
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
    // Isabelle rejects names ending in an underscore
    while out.ends_with('_') {
        out.pop();
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

/// Rust path segments as one identifier.
fn joined(segments: &[String]) -> String {
    segments.iter().map(|s| ident_chars(s)).collect::<Vec<_>>().join("_")
}

/// Name of a top-level HOL constant derived from Rust path segments.
pub fn global_name(segments: &[String]) -> String {
    let base = joined(segments);
    if is_reserved(&base) || OUTER_KEYWORDS.contains(&base.as_str()) { format!("{}_fn", base) } else { base }
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

/// Name of a HOL type derived from Rust path segments.
pub fn type_name(segments: &[String]) -> String {
    let base = joined(segments);
    if RESERVED_TYPES.contains(&base.as_str()) || OUTER_KEYWORDS.contains(&base.as_str()) {
        format!("{}_t", base)
    } else {
        base
    }
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
