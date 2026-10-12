//! Each test translates Rust crates with the frontend and checks the generated theories
//! with Isabelle, in a memory-capped Isabelle server of its own, with a time limit per crate.
//!
//! Run: `scripts/cargo.sh test --release -- --test-threads=1 --nocapture`

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::Duration;

// ---------------------------------------------------------------------------------------
// Common data
// ---------------------------------------------------------------------------------------

/// Memory cap of the Isabelle server (systemd scope); override with `MEMORY_MAX`.
fn memory_max() -> String {
    std::env::var("MEMORY_MAX").unwrap_or_else(|_| "4G".into())
}

/// Time limit for checking one crate.
const CRATE_TIMEOUT_SECS: u64 = 300;

/// AutoCorrode checkout whose session `AutoCorrode` contains the signed-integer and
/// break/continue extensions; it must be given explicitly.
fn autocorrode() -> String {
    std::env::var("AUTOCORRODE").expect("set AUTOCORRODE to the AutoCorrode checkout to test against")
}

fn isabelle() -> String {
    std::env::var("ISABELLE")
        .unwrap_or_else(|_| format!("{}/Applications/Isabelle2025-2/bin/isabelle", std::env::var("HOME").unwrap()))
}

/// Every crate, in `tests/crates` or in a test below, is compiled as a library with these
/// rustc arguments.
const RUSTC_ARGS: &[&str] = &["--edition=2021"];

/// `tests/crates`: one library crate per `.rs` file, each compiled by plain rustc with
/// `RUSTC_ARGS`. Taken unchanged from github.com/AeneasVerif/aeneas (tests/src, Apache-2.0),
/// github.com/AeneasVerif/charon (charon/tests/ui, Apache-2.0) and
/// github.com/TheAlgorithms/Rust (src, MIT).
const CRATES_DIR: &str = "tests/crates";


// ---------------------------------------------------------------------------------------
// Translation
// ---------------------------------------------------------------------------------------

enum Translation {
    /// Theories in `dir`, entry theory `NAME_Funs`, with this many placeholders.
    Translated { dir: PathBuf, name: String, placeholders: usize },
    RustcRejected(String),
    FrontendCrashed(String),
}

/// Libraries of the compiler the frontend links against.
fn toolchain_lib() -> String {
    let rustc = std::env::var("CARGO_HOME").map(|h| format!("{}/bin/rustc", h)).unwrap_or_else(|_| "rustc".into());
    let out = Command::new(rustc).args(["--print", "sysroot"]).output().expect("rustc --print sysroot");
    let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
    format!("{0}/lib:{0}/lib/rustlib/x86_64-unknown-linux-gnu/lib", sysroot)
}

fn run_frontend(file: &Path, name: &str, out: &Path, args: &[String]) -> (bool, String) {
    let _ = std::fs::remove_dir_all(out);
    let o = Command::new(env!("CARGO_BIN_EXE_urust-frontend"))
        .arg("--out")
        .arg(out)
        .arg("--name")
        .arg(name)
        .arg(file)
        .arg("--")
        .args(args)
        .env("LD_LIBRARY_PATH", toolchain_lib())
        .output()
        .expect("run frontend");
    (o.status.success(), String::from_utf8_lossy(&o.stderr).into_owned())
}

fn translate(file: &Path, name: &str, out: &Path) -> Translation {
    let args: Vec<String> = RUSTC_ARGS.iter().map(|a| a.to_string()).collect();
    let (ok, log) = run_frontend(file, name, out, &args);
    let funs = out.join(format!("{}_Funs.thy", name));
    if ok && funs.exists() {
        let rep = std::fs::read_to_string(out.join("PLACEHOLDERS.txt")).unwrap_or_default();
        let n = rep.lines().next().and_then(|l| l.rsplit(": ").next()).and_then(|n| n.trim().parse().ok()).unwrap_or(0);
        Translation::Translated { dir: out.to_path_buf(), name: name.to_string(), placeholders: n }
    } else if log.contains("panicked at") || log.contains("internal compiler error") {
        Translation::FrontendCrashed(first_line_with(&log, "panicked"))
    } else {
        Translation::RustcRejected(first_line_with(&log, "error"))
    }
}

fn first_line_with(log: &str, key: &str) -> String {
    log.lines().find(|l| l.contains(key)).unwrap_or("").chars().take(160).collect()
}

// ---------------------------------------------------------------------------------------
// Isabelle server: one per test, memory-capped; one crate is checked at a time and purged
// ---------------------------------------------------------------------------------------

struct Server {
    child: Child,
    writer: TcpStream,
    reader: BufReader<TcpStream>,
    session_id: String,
}

enum Check {
    Accepted,
    Rejected(String),
    /// The server died or did not answer in time (memory or time limit).
    Aborted(String),
}

fn json_str_field(msg: &str, field: &str) -> Option<String> {
    let key = format!("\"{}\":\"", field);
    let start = msg.find(&key)? + key.len();
    let mut out = String::new();
    let mut esc = false;
    for c in msg[start..].chars() {
        if esc {
            out.push(match c { 'n' => ' ', c => c });
            esc = false;
        } else if c == '\\' {
            esc = true;
        } else if c == '"' {
            return Some(out);
        } else {
            out.push(c);
        }
    }
    None
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

impl Server {
    fn start(tag: &str) -> Server {
        let name = format!("urust-test-{}-{}", tag, std::process::id());
        let mut child = Command::new("systemd-run")
            .args(["--user", "--scope", "-q", "-p", &format!("MemoryMax={}", memory_max()), "-p", "MemorySwapMax=0"])
            .arg(isabelle())
            .args(["server", "-n", &name])
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("start isabelle server");
        let mut first = String::new();
        BufReader::new(child.stdout.take().unwrap()).read_line(&mut first).expect("server banner");
        // server "NAME" = 127.0.0.1:PORT (password "PW")
        let addr = first.split(" = ").nth(1).and_then(|r| r.split_whitespace().next()).expect("server address");
        let password = first.split("password \"").nth(1).and_then(|r| r.split('"').next()).expect("server password");
        let stream = TcpStream::connect(addr).expect("connect to server");
        let mut s = Server {
            child,
            writer: stream.try_clone().unwrap(),
            reader: BufReader::new(stream),
            session_id: String::new(),
        };
        s.send(password);
        let started = s
            .task(&format!(
                "session_start {{\"session\":\"AutoCorrode\",\"dirs\":[\"{}\"],\"options\":[\"threads=2\"]}}",
                json_escape(&autocorrode())
            ))
            .expect("session_start");
        s.session_id = json_str_field(&started, "session_id").expect("session id");
        s
    }

    fn send(&mut self, line: &str) {
        let _ = self.writer.write_all(line.as_bytes());
        let _ = self.writer.write_all(b"\n");
        let _ = self.writer.flush();
    }

    fn recv(&mut self) -> Result<String, String> {
        let mut line = String::new();
        match self.reader.read_line(&mut line) {
            Ok(0) => return Err("server connection closed".into()),
            Err(e) => return Err(format!("server: {}", e)),
            Ok(_) => {}
        }
        let line = line.trim_end_matches(['\r', '\n']).to_string();
        if !line.is_empty() && line.bytes().all(|b| b.is_ascii_digit()) {
            let mut buf = vec![0u8; line.parse::<usize>().unwrap()];
            self.reader.read_exact(&mut buf).map_err(|e| format!("server: {}", e))?;
            return Ok(String::from_utf8_lossy(&buf).trim_end().to_string());
        }
        Ok(line)
    }

    /// Run an asynchronous command; its FINISHED result, or the reason of failure.
    fn task(&mut self, cmd: &str) -> Result<String, String> {
        self.send(cmd);
        let first = self.recv()?;
        if !first.starts_with("OK") {
            return Err(first);
        }
        loop {
            let m = self.recv()?;
            if m.starts_with("FINISHED") {
                return Ok(m);
            }
            if m.starts_with("FAILED") {
                return Err(json_str_field(&m, "message").unwrap_or(m));
            }
        }
    }

    fn check(&mut self, dir: &Path, theory: &str) -> Check {
        let limit = CRATE_TIMEOUT_SECS * 2; // check_delay 0.5 s
        self.writer.set_read_timeout(Some(Duration::from_secs(CRATE_TIMEOUT_SECS + 60))).ok();
        self.reader.get_ref().set_read_timeout(Some(Duration::from_secs(CRATE_TIMEOUT_SECS + 60))).ok();
        let res = self.task(&format!(
            "use_theories {{\"session_id\":\"{}\",\"theories\":[\"{}\"],\"master_dir\":\"{}\",\"check_delay\":0.5,\"check_limit\":{},\"watchdog_timeout\":{}}}",
            self.session_id,
            theory,
            json_escape(&dir.to_string_lossy()),
            limit,
            CRATE_TIMEOUT_SECS
        ));
        let out = match res {
            Err(e) => Check::Aborted(e),
            Ok(m) if m.contains("\"ok\":true") && m.contains("\"errors\":[]") => Check::Accepted,
            Ok(m) => {
                let errs = m.split("\"errors\":").nth(1).unwrap_or("");
                Check::Rejected(json_str_field(errs, "message").unwrap_or_else(|| "not finished".into()))
            }
        };
        if !matches!(out, Check::Aborted(_)) {
            self.send(&format!("purge_theories {{\"session_id\":\"{}\",\"all\":true}}", self.session_id));
            let _ = self.recv();
        }
        out
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.send("shutdown");
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

// ---------------------------------------------------------------------------------------
// Single-crate tests: the Rust source is given in the test
// ---------------------------------------------------------------------------------------

struct Outcome {
    accepted: bool,
    placeholders: usize,
    detail: String,
}

fn check_source(test: &str, src: &str) -> Outcome {
    let base = std::env::temp_dir().join(format!("urust-frontend-test-{}-{}", test, std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(&base).unwrap();
    let file = base.join(format!("{}.rs", test));
    std::fs::write(&file, src).unwrap();
    let name = format!("T_{}", test);
    let out = match translate(&file, &name, &base.join("out")) {
        Translation::Translated { dir, name, placeholders } => {
            let mut server = Server::start(test);
            match server.check(&dir, &format!("{}_Funs", name)) {
                Check::Accepted => Outcome { accepted: true, placeholders, detail: String::new() },
                Check::Rejected(e) | Check::Aborted(e) => Outcome { accepted: false, placeholders, detail: e },
            }
        }
        Translation::RustcRejected(e) => Outcome { accepted: false, placeholders: 0, detail: format!("rustc: {}", e) },
        Translation::FrontendCrashed(e) => Outcome { accepted: false, placeholders: 0, detail: format!("frontend: {}", e) },
    };
    let _ = std::fs::remove_dir_all(&base);
    out
}

/// The generated program is accepted and contains no placeholder.
fn supported(test: &str, src: &str) {
    let o = check_source(test, src);
    assert!(o.accepted, "not accepted: {}", o.detail);
    assert_eq!(o.placeholders, 0, "unexpected placeholders");
}

/// The generated program is accepted and contains a placeholder for the unsupported feature.
fn unsupported(test: &str, src: &str) {
    let o = check_source(test, src);
    assert!(o.accepted, "not accepted: {}", o.detail);
    assert!(o.placeholders > 0, "no placeholder generated");
}

#[test]
fn arithmetic() {
    supported("arithmetic", "pub fn f(a: u32, b: u32) -> u32 { (a + b) * 2 - a / 3 % 7 }");
}

#[test]
fn if_else_value() {
    supported("if_else_value", "pub fn f(a: u64, b: u64) -> u64 { let m = if a > b { a } else { b }; m }");
}

#[test]
fn while_loop_mutable_local() {
    supported(
        "while_loop_mutable_local",
        "pub fn f(n: u32) -> u32 { let mut s = 0; let mut i = 0; while i < n { i += 1; s += i; } s }",
    );
}

#[test]
fn compound_assignment() {
    supported(
        "compound_assignment",
        "pub fn f(mut x: u32) -> u32 { x -= 1; x *= 3; x %= 5; x &= 7; x |= 8; x ^= 1; x <<= 2; x >>= 1; x /= 2; x }",
    );
}

#[test]
fn casts_between_integers() {
    supported("casts_between_integers", "pub fn f(a: u8, b: u64, c: i8) -> u32 { a as u32 + b as u32 + (c as i64) as u32 }");
}

#[test]
fn bitwise_and_shifts() {
    supported("bitwise_and_shifts", "pub fn f(x: u8, y: u8) -> u8 { ((x & y) ^ (x | y)) << 1 >> 2 }");
}

#[test]
fn boolean_logic() {
    supported("boolean_logic", "pub fn f(x: u16) -> bool { x >= 3 && x <= 10 || !(x != 7) }");
}

#[test]
fn early_return() {
    supported("early_return", "pub fn f(x: u32) -> u32 { if x == 0 { return 1; } x * 2 }");
}

#[test]
fn deferred_initialisation() {
    supported("deferred_initialisation", "pub fn f(c: bool) -> u32 { let x; if c { x = 1; } else { x = 2; } x }");
}

#[test]
fn constants() {
    supported("constants", "pub const LIMIT: u32 = 100; pub fn f(x: u32) -> bool { x < LIMIT && x < u32::MAX }");
}

#[test]
fn char_and_string_literals() {
    supported("char_and_string_literals", "pub fn f(c: char) -> bool { let _s: &str = \"hello\"; c == 'a' || c == '\\n' }");
}

#[test]
fn struct_construction_and_fields() {
    supported(
        "struct_construction_and_fields",
        "pub struct P { pub x: u32, pub y: u32 } pub fn f(a: u32) -> u32 { let p = P { y: 2, x: a }; p.x + p.y }",
    );
}

#[test]
fn method_with_mut_self() {
    supported(
        "method_with_mut_self",
        "pub struct P { pub x: u32 }
         impl P { pub fn bump(&mut self, d: u32) { self.x += d; } pub fn get(&self) -> u32 { self.x } }
         pub fn f() -> u32 { let mut p = P { x: 1 }; p.bump(2); p.get() }",
    );
}

#[test]
fn nested_field_update() {
    supported(
        "nested_field_update",
        "pub struct A { pub x: u32 } pub struct B { pub a: A, pub w: u32 }
         pub fn f() -> u32 { let mut b = B { a: A { x: 1 }, w: 2 }; b.a.x += 5; b.w = 4; b.a.x + b.w }",
    );
}

#[test]
fn tuple_and_unit_structs() {
    supported(
        "tuple_and_unit_structs",
        "pub struct M(pub u64); pub struct U; pub fn f(m: M) -> u64 { let M(v) = m; let _u = U; v + m.0 }",
    );
}

#[test]
fn struct_update_syntax() {
    supported(
        "struct_update_syntax",
        "#[derive(Clone, Copy)] pub struct P { pub x: u32, pub y: u32 } pub fn f(p: P) -> P { P { x: 7, ..p } }",
    );
}

#[test]
fn struct_destructuring() {
    supported("struct_destructuring", "pub struct P { pub x: u32, pub y: u32 } pub fn f(p: P) -> u32 { let P { x, y } = p; x * y }");
}

#[test]
fn derived_equality_and_clone() {
    supported(
        "derived_equality_and_clone",
        "#[derive(Clone, Copy, PartialEq)] pub struct P { pub x: u32 } pub fn f(a: P, b: P) -> bool { a.clone() == b }",
    );
}

#[test]
fn enum_match() {
    supported(
        "enum_match",
        "pub enum S { C(u32), R { w: u32, h: u32 }, E }
         pub fn f(s: &S) -> u32 { match s { S::C(r) => 3 * r, S::R { w, h } => w * h, S::E => 0 } }",
    );
}

#[test]
fn guards_and_literal_subpatterns() {
    supported(
        "guards_and_literal_subpatterns",
        "pub enum S { C(u32), E } pub fn f(s: S) -> u32 { match s { S::C(r) if r > 10 => 1, S::C(0) => 2, S::C(r) => r, S::E => 4 } }",
    );
}

#[test]
fn or_patterns() {
    supported(
        "or_patterns",
        "#[derive(Clone, Copy)] pub enum C { R, G, B } pub fn f(c: C) -> u8 { match c { C::R | C::G => 1, C::B => 2 } }",
    );
}

#[test]
fn matches_macro() {
    supported("matches_macro", "pub enum C { R, G } pub fn f(c: C) -> bool { matches!(c, C::R) }");
}

#[test]
fn question_mark_on_option() {
    supported("question_mark_on_option", "pub fn f(a: Option<u32>) -> Option<u32> { let x = a?; Some(x + 1) }");
}

#[test]
fn question_mark_on_result() {
    supported(
        "question_mark_on_result",
        "pub fn f(a: Result<u32, u8>) -> Result<u32, u8> { let x = a?; if x > 9 { return Err(1); } Ok(x) }",
    );
}

#[test]
fn if_let() {
    supported("if_let", "pub fn f(a: Option<u64>) -> u64 { if let Some(v) = a { v } else { 0 } }");
}

#[test]
fn let_else() {
    supported("let_else", "pub fn f(a: Option<u32>) -> u32 { let Some(v) = a else { return 0; }; v + 1 }");
}

#[test]
fn while_let() {
    supported(
        "while_let",
        "pub fn f(s: Option<u32>) -> u32 { let mut c = s; let mut n = 0; while let Some(v) = c { n += 1; c = if v == 0 { None } else { Some(v - 1) }; } n }",
    );
}

#[test]
fn tuple_scrutinee() {
    supported(
        "tuple_scrutinee",
        "pub fn f(a: Option<u32>, b: Option<u32>) -> u32 { match (a, b) { (Some(x), Some(y)) => x + y, (Some(x), None) => x, (None, _) => 0 } }",
    );
}

#[test]
fn binding_with_range() {
    supported("binding_with_range", "pub fn f(a: Option<u32>) -> u32 { match a { Some(n @ 1..=9) => n, Some(n) => n + 100, None => 0 } }");
}

#[test]
fn mutable_pattern_binding() {
    supported("mutable_pattern_binding", "pub fn f(a: Option<u32>) -> u32 { match a { Some(mut v) => { v += 1; v } None => 0 } }");
}

#[test]
fn integer_match() {
    supported("integer_match", "pub fn f(x: u8) -> u8 { match x { 0 => 10, 1 | 2 => 20, 4..=9 => 30, n if n > 200 => n - 200, _ => 40 } }");
}

#[test]
fn char_and_str_match() {
    supported(
        "char_and_str_match",
        "pub fn f(c: char, s: &str) -> u32 { (match c { 'a' => 1, _ => 2 }) + (match s { \"one\" => 1, _ => 0 }) }",
    );
}

#[test]
fn for_over_ranges() {
    supported(
        "for_over_ranges",
        "pub fn f(n: u64) -> u64 { let mut s = 0; for i in 0..n { s += i; } for i in 1..=n { s += i; } s }",
    );
}

#[test]
fn for_over_collections() {
    supported(
        "for_over_collections",
        "pub fn f(v: &Vec<u32>, w: &[u32]) -> u32 { let a = [1u32, 2]; let mut s = 0; for x in v.iter() { s += x; } for x in w { s += x; } for x in a.iter() { s += *x; } s }",
    );
}

#[test]
fn labeled_break_and_continue() {
    supported(
        "labeled_break_and_continue",
        "pub fn f(n: u32) -> u32 { let mut c = 0; 'o: for i in 0..n { for j in 0..n { if j > i { continue 'o; } if i + j > 10 { break 'o; } c += 1; } } c }",
    );
}

#[test]
fn loop_with_break() {
    supported("loop_with_break", "pub fn f(n: u32) -> u32 { let mut i = 0; loop { if i * i >= n { break; } i += 1; } i }");
}

#[test]
fn recursion() {
    supported("recursion", "pub fn fact(n: u64) -> u64 { if n == 0 { 1 } else { n * fact(n - 1) } }");
}

#[test]
fn mutual_recursion() {
    supported(
        "mutual_recursion",
        "pub fn even(n: u32) -> bool { if n == 0 { true } else { odd(n - 1) } } pub fn odd(n: u32) -> bool { if n == 0 { false } else { even(n - 1) } }",
    );
}

#[test]
fn recursive_types() {
    supported(
        "recursive_types",
        "pub enum L { N, C(u32, Box<L>) } pub fn sum(l: &L) -> u32 { match l { L::N => 0, L::C(v, r) => v + sum(r) } }",
    );
}

#[test]
fn mutually_recursive_types() {
    supported(
        "mutually_recursive_types",
        "pub enum E { L(u32), N(Box<T>) } pub enum T { A(u32), W(Box<E>) }
         pub fn ev(e: &E) -> u32 { match e { E::L(v) => *v, E::N(t) => et(t) } }
         pub fn et(t: &T) -> u32 { match t { T::A(v) => *v, T::W(e) => ev(e) } }",
    );
}

#[test]
fn signed_arithmetic() {
    supported("signed_arithmetic", "pub fn f(a: i32, b: i32) -> (i32, i32) { (-a / b, (a % b) >> 1) }");
}

#[test]
fn signed_literals_and_casts() {
    supported("signed_literals_and_casts", "pub fn f(a: i8, b: u8) -> i64 { let c: i32 = -5; a as i64 + b as i64 + c as i64 + i64::MIN / 2 }");
}

#[test]
fn signed_match() {
    supported("signed_match", "pub fn f(x: i32) -> i32 { match x { 0 => 0, -1 => -1, i32::MIN..=-2 => -2, _ => 1 } }");
}

#[test]
fn signed_range_loop() {
    supported("signed_range_loop", "pub fn f(n: i32) -> i32 { let mut s = 0; for i in -3..n { s += i; } s }");
}

#[test]
fn mutable_reference_parameters() {
    supported(
        "mutable_reference_parameters",
        "pub fn swap(a: &mut u32, b: &mut u32) { let t = *a; *a = *b; *b = t; } pub fn f() -> u32 { let mut x = 1; let mut y = 2; swap(&mut x, &mut y); x }",
    );
}

#[test]
fn mutable_borrow_of_field() {
    supported(
        "mutable_borrow_of_field",
        "pub struct C { pub hits: u32 } pub fn inc(c: &mut u32) { *c += 1; } pub fn f(c: &mut C) { inc(&mut c.hits); }",
    );
}

#[test]
fn vec_index_through_reference() {
    supported("vec_index_through_reference", "pub fn f(v: &mut Vec<u64>, i: usize) { v[i] = 5; v[0] += v[i]; }");
}

#[test]
fn reborrow() {
    supported("reborrow", "pub fn f(a: &mut u32) { let r = &mut *a; *r = 3; }");
}

#[test]
fn struct_with_reference_field() {
    supported("struct_with_reference_field", "pub struct H<'a> { pub r: &'a mut u32 } pub fn f(h: H) { *h.r = 1; }");
}

#[test]
fn generic_function_and_struct() {
    supported(
        "generic_function_and_struct",
        "pub struct W<T> { pub v: T } pub fn id<T>(x: T) -> T { x } pub fn f(x: u32) -> u32 { let w = W { v: x }; id(w.v) }",
    );
}

#[test]
fn trait_implementation_call() {
    supported(
        "trait_implementation_call",
        "pub trait A { fn area(&self) -> u32; } pub struct S(pub u32); impl A for S { fn area(&self) -> u32 { self.0 * self.0 } } pub fn f(s: &S) -> u32 { s.area() }",
    );
}

#[test]
fn operator_overloading() {
    supported(
        "operator_overloading",
        "use std::ops::Add; #[derive(Clone, Copy)] pub struct V { pub a: u32 }
         impl Add for V { type Output = V; fn add(self, o: V) -> V { V { a: self.a + o.a } } }
         pub fn f(x: V, y: V) -> V { x + y }",
    );
}

#[test]
fn closures() {
    supported("closures", "pub fn f(x: u32, k: u32) -> u32 { let g = |v: u32| v * k; let h = || 5u32; g(x) + h() }");
}

#[test]
fn standard_library_models() {
    supported(
        "standard_library_models",
        "pub fn f(a: Option<u32>, r: Result<u32, u8>, v: Vec<u8>) -> u64 { let x = a.unwrap() + r.unwrap(); let n = v.len() as u64; if a.is_some() && r.is_ok() { n + x as u64 } else { 0 } }",
    );
}

#[test]
fn external_function_template() {
    supported("external_function_template", "pub fn f(n: u32) -> usize { let mut v: Vec<u32> = Vec::new(); v.push(n); v.len() }");
}

#[test]
fn assertions_and_panics() {
    supported("assertions_and_panics", "pub fn f(x: u32) -> u32 { assert!(x > 0); if x == 5 { panic!(\"five\"); } x }");
}

#[test]
fn modules_and_nested_items() {
    supported(
        "modules_and_nested_items",
        "pub mod m { pub fn g(x: u32) -> u32 { x + 1 } } pub fn f(a: u32) -> u32 { fn h(v: u32) -> u32 { v * 2 } const K: u32 = 4; m::g(h(a)) + K }",
    );
}

#[test]
fn names_clashing_with_isabelle_keywords() {
    supported("names_clashing_with_isabelle_keywords", "pub fn record(len: u32, of: u32, choose: u32) -> u32 { len + of + choose } pub fn step() -> u32 { record(1, 2, 3) }");
}

#[test]
fn nine_argument_call() {
    supported(
        "nine_argument_call",
        "pub fn g(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, h: u8, i: u8, j: u8) -> u8 { a + b + c + d + e + f + h + i + j } pub fn f() -> u8 { g(1, 2, 3, 4, 5, 6, 7, 8, 9) }",
    );
}

#[test]
fn unsupported_float() {
    unsupported("unsupported_float", "pub fn f(x: f64) -> f64 { x * 2.5 }");
}

#[test]
fn unsupported_u128() {
    unsupported("unsupported_u128", "pub fn f(x: u128) -> u128 { x + 1 }");
}

#[test]
fn unsupported_dynamic_dispatch() {
    unsupported("unsupported_dynamic_dispatch", "pub trait S { fn a(&self) -> u32; } pub fn f(s: &dyn S) -> u32 { s.a() }");
}

#[test]
fn unsupported_trait_call_in_generic_code() {
    unsupported("unsupported_trait_call_in_generic_code", "pub trait S { fn a(&self) -> u32; } pub fn f<T: S>(s: &T) -> u32 { s.a() + 1 }");
}

#[test]
fn unsupported_async() {
    unsupported("unsupported_async", "pub async fn f() -> u32 { 1 }");
}

#[test]
fn unsupported_union() {
    unsupported("unsupported_union", "pub union U { pub a: u32, pub b: f32 }");
}

#[test]
fn unsupported_static_mut() {
    unsupported("unsupported_static_mut", "pub static mut C: u32 = 0;");
}

#[test]
fn unsupported_raw_pointer() {
    unsupported("unsupported_raw_pointer", "pub fn f(p: *const u32) -> u32 { unsafe { *p } }");
}

#[test]
fn unsupported_break_with_value() {
    unsupported("unsupported_break_with_value", "pub fn f(n: u32) -> u32 { let mut i = 0; let r = loop { i += 1; if i > n { break i; } }; r }");
}

#[test]
fn unsupported_labeled_block() {
    unsupported("unsupported_labeled_block", "pub fn f(c: bool) -> u32 { 'b: { if c { break 'b 1; } 2 } }");
}

#[test]
fn unsupported_array_repeat() {
    unsupported("unsupported_array_repeat", "pub fn f() -> u8 { let a = [0u8; 4]; a[1] }");
}

#[test]
fn unsupported_closure_mutating_capture() {
    unsupported("unsupported_closure_mutating_capture", "pub fn f() -> u32 { let mut n = 0; let mut inc = || n += 1; inc(); n }");
}

#[test]
fn unsupported_ref_binding() {
    unsupported("unsupported_ref_binding", "pub fn f(o: &Option<u32>) -> u32 { match *o { Some(ref v) => *v, None => 0 } }");
}

#[test]
fn unsupported_slice_rest_pattern() {
    unsupported("unsupported_slice_rest_pattern", "pub fn f(v: &[u32]) -> u32 { match v { [a, ..] => *a, [] => 0 } }");
}

#[test]
fn unsupported_const_generic() {
    unsupported("unsupported_const_generic", "pub fn f<const N: usize>(a: [u8; N]) -> usize { N + a.len() }");
}

#[test]
fn unsupported_impl_trait_result() {
    unsupported("unsupported_impl_trait_result", "pub fn f() -> impl Fn(u32) -> u32 { |x| x + 1 }");
}

#[test]
fn unsupported_string_formatting() {
    unsupported("unsupported_string_formatting", "pub fn f(x: u32) -> String { format!(\"{}\", x) }");
}

#[test]
fn unsupported_enum_cast() {
    unsupported("unsupported_enum_cast", "pub enum D { A = 1, B = 5 } pub fn f(d: D) -> u32 { d as u32 }");
}

#[test]
fn unsupported_interior_mutability() {
    unsupported("unsupported_interior_mutability", "use std::cell::Cell; pub fn f(c: &Cell<u32>) { c.set(c.get() + 1); }");
}

#[test]
fn unsupported_byte_string() {
    unsupported("unsupported_byte_string", "pub fn f() -> &'static [u8] { b\"abc\" }");
}

#[test]
fn unsupported_bool_cast() {
    unsupported("unsupported_bool_cast", "pub fn f(b: bool) -> u32 { b as u32 }");
}

#[test]
fn unsupported_inline_const() {
    unsupported("unsupported_inline_const", "pub fn f() -> u32 { const { 1 + 2 } }");
}

#[test]
fn assert_eq_macro() {
    supported("assert_eq_macro", "pub fn f(x: u32, y: u32) -> u32 { assert_eq!(x, y); x }");
}

// ---------------------------------------------------------------------------------------
// tests/crates: every crate is translated and checked on its own
// ---------------------------------------------------------------------------------------

#[test]
fn crates() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(CRATES_DIR);
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("tests/crates")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .collect();
    files.sort();
    let work = std::env::temp_dir().join(format!("urust-frontend-crates-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&work);
    let mut server: Option<Server> = None;
    let (mut accepted, mut clean) = (0, 0);
    let mut failures: Vec<String> = vec![];
    for f in &files {
        let stem: String =
            f.file_stem().unwrap().to_string_lossy().chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
        match translate(f, &format!("C_{}", stem), &work.join(&stem)) {
            Translation::RustcRejected(e) => failures.push(format!("{}: rejected by rustc: {}", stem, e)),
            Translation::FrontendCrashed(e) => failures.push(format!("{}: frontend crash: {}", stem, e)),
            Translation::Translated { dir, name, placeholders } => {
                let srv = server.get_or_insert_with(|| Server::start("crates"));
                match srv.check(&dir, &format!("{}_Funs", name)) {
                    Check::Accepted => {
                        accepted += 1;
                        if placeholders == 0 {
                            clean += 1;
                        }
                    }
                    Check::Rejected(e) => failures.push(format!("{}: rejected by Isabelle: {}", stem, e)),
                    Check::Aborted(e) => {
                        failures.push(format!("{}: aborted (time or memory limit): {}", stem, e));
                        server = None;
                    }
                }
                let _ = std::fs::remove_dir_all(&dir);
            }
        }
    }
    let n = files.len();
    let pct = |a: usize| if n == 0 { 0.0 } else { 100.0 * a as f64 / n as f64 };
    println!(
        "crates: {}, accepted by Isabelle: {} ({:.1}%), accepted without placeholders: {} ({:.1}%)",
        n,
        accepted,
        pct(accepted),
        clean,
        pct(clean)
    );
    for l in &failures {
        println!("  {}", l);
    }
    assert!(failures.is_empty(), "{} of {} crates failed", failures.len(), n);
}
