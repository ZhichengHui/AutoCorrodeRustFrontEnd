//! Translates every crate in `tests/crates` with the frontend and checks the generated
//! theories with Isabelle: one memory-capped Isabelle server loads the AutoCorrode heap once
//! and checks the crates one at a time, each with a time limit. Prints the outcome of every
//! crate and the number of crates per outcome.
//!
//! Run: `scripts/cargo.sh test --release -- --nocapture`. With `CRATE_FILTER=TEXT`, only the
//! crates whose file name contains TEXT are checked.

use serde_json::{Value, json};
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

/// Every crate is compiled as a library with these rustc arguments.
const RUSTC_ARGS: &[&str] = &["--edition=2024"];

/// `tests/crates`: one library crate per `.rs` file, each compiled by plain rustc with
/// `RUSTC_ARGS`. `aeneas__*`, `charon__*` and `algorithms__*` are taken from
/// github.com/AeneasVerif/aeneas (tests/src, Apache-2.0), github.com/AeneasVerif/charon
/// (charon/tests/ui, Apache-2.0) and github.com/TheAlgorithms/Rust (src, MIT); unchanged
/// except for the edition-2024 edits listed in `tests/crates/EDITION_2024.md`.
/// `handwritten__*` are written for this frontend, each exercising one language feature or
/// a few related ones.
const CRATES_DIR: &str = "tests/crates";

// ---------------------------------------------------------------------------------------
// Translation
// ---------------------------------------------------------------------------------------

enum Translation {
    /// Theories in `dir`, entry theory `NAME_Funs`; whether the frontend reported a placeholder.
    Translated { dir: PathBuf, name: String, placeholders: bool },
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

fn translate(file: &Path, name: &str, out: &Path) -> Translation {
    let _ = std::fs::remove_dir_all(out);
    let o = Command::new(env!("CARGO_BIN_EXE_urust-frontend"))
        .arg("--out")
        .arg(out)
        .arg("--name")
        .arg(name)
        .arg(file)
        .arg("--")
        .args(RUSTC_ARGS)
        .env("LD_LIBRARY_PATH", toolchain_lib())
        .output()
        .expect("run frontend");
    let log = String::from_utf8_lossy(&o.stderr);
    match o.status.code() {
        Some(0) => {
            // One line `- ...` per placeholder.
            let report = std::fs::read_to_string(out.join("PLACEHOLDERS.txt")).expect("PLACEHOLDERS.txt");
            Translation::Translated {
                dir: out.to_path_buf(),
                name: name.to_string(),
                placeholders: report.lines().any(|l| l.starts_with("- ")),
            }
        }
        // rustc_driver exits with 1 on compile errors; a panic (frontend bug or ICE) exits with 101.
        Some(101) => Translation::FrontendCrashed(first_line_with(&log, "panicked")),
        _ => Translation::RustcRejected(first_line_with(&log, "error")),
    }
}

fn first_line_with(log: &str, key: &str) -> String {
    log.lines().find(|l| l.contains(key)).unwrap_or("").chars().take(160).collect()
}

// ---------------------------------------------------------------------------------------
// Isabelle server: memory-capped; one crate is checked at a time and purged
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
    /// The server died, did not answer, or did not finish the check in time.
    Aborted(String),
}

impl Server {
    fn start() -> Server {
        let name = format!("urust-test-{}", std::process::id());
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
            .task("session_start", json!({"session": "AutoCorrode", "dirs": [autocorrode()], "options": ["threads=2"]}))
            .expect("session_start");
        s.session_id = started["session_id"].as_str().expect("session id").to_string();
        s
    }

    fn send(&mut self, line: &str) {
        let _ = self.writer.write_all(line.as_bytes());
        let _ = self.writer.write_all(b"\n");
        let _ = self.writer.flush();
    }

    /// One message; a long message is sent as a line with its byte length, then the message.
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

    /// Run an asynchronous command; the argument of its FINISHED reply, or the reason of failure.
    fn task(&mut self, cmd: &str, arg: Value) -> Result<Value, String> {
        self.send(&format!("{} {}", cmd, arg));
        let first = self.recv()?;
        if !first.starts_with("OK") {
            return Err(first);
        }
        loop {
            let m = self.recv()?;
            let (kind, rest) = m.split_once(' ').unwrap_or((&m, ""));
            match kind {
                "FINISHED" => return serde_json::from_str(rest).map_err(|e| format!("server reply: {}", e)),
                "FAILED" => {
                    let v: Value = serde_json::from_str(rest).unwrap_or(Value::Null);
                    return Err(v["message"].as_str().unwrap_or(rest).to_string());
                }
                _ => {}
            }
        }
    }

    fn check(&mut self, dir: &Path, theory: &str) -> Check {
        // The server enforces the time limit; the read timeout only guards against a hung server.
        let guard = Some(Duration::from_secs(CRATE_TIMEOUT_SECS + 60));
        self.reader.get_ref().set_read_timeout(guard).ok();
        let res = self.task(
            "use_theories",
            json!({
                "session_id": self.session_id,
                "theories": [theory],
                "master_dir": dir.to_string_lossy(),
                "check_delay": 0.5,
                "check_limit": CRATE_TIMEOUT_SECS * 2,
            }),
        );
        let out = match res {
            Err(e) => Check::Aborted(e),
            Ok(v) => match v["errors"].as_array().and_then(|errs| errs.first()) {
                Some(e) => Check::Rejected(e["message"].as_str().unwrap_or("").chars().take(160).collect()),
                None if v["ok"] == true => Check::Accepted,
                None => Check::Aborted("not finished within the time limit".into()),
            },
        };
        if !matches!(out, Check::Aborted(_)) {
            // Synchronous command: a single OK reply.
            self.send(&format!("purge_theories {}", json!({"session_id": self.session_id, "all": true})));
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
// tests/crates: every crate is translated and checked on its own
// ---------------------------------------------------------------------------------------

#[test]
fn crates() {
    let filter = std::env::var("CRATE_FILTER").unwrap_or_default();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(CRATES_DIR);
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("tests/crates")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .filter(|p| p.file_name().unwrap().to_string_lossy().contains(&filter))
        .collect();
    files.sort();
    let work = std::env::temp_dir().join(format!("urust-frontend-crates-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&work);
    let mut server: Option<Server> = None;
    // rustc rejected, frontend crashed, Isabelle rejected, aborted, accepted with / without placeholders
    let mut counts = [0usize; 6];
    for f in &files {
        let stem: String =
            f.file_stem().unwrap().to_string_lossy().chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
        let (i, outcome) = match translate(f, &format!("C_{}", stem), &work.join(&stem)) {
            Translation::RustcRejected(e) => (0, format!("rejected by rustc: {}", e)),
            Translation::FrontendCrashed(e) => (1, format!("frontend crashed: {}", e)),
            Translation::Translated { dir, name, placeholders } => {
                let srv = server.get_or_insert_with(Server::start);
                let r = match srv.check(&dir, &format!("{}_Funs", name)) {
                    Check::Rejected(e) => (2, format!("rejected by Isabelle: {}", e)),
                    Check::Aborted(e) => {
                        server = None;
                        (3, format!("aborted (time or memory limit): {}", e))
                    }
                    Check::Accepted if placeholders => (4, "accepted, with placeholders".to_string()),
                    Check::Accepted => (5, "accepted, without placeholders".to_string()),
                };
                let _ = std::fs::remove_dir_all(&dir);
                r
            }
        };
        counts[i] += 1;
        println!("{}: {}", stem, outcome);
    }
    println!("crates: {}", files.len());
    println!("  rejected by rustc: {}", counts[0]);
    println!("  frontend crashed: {}", counts[1]);
    println!("  rejected by Isabelle: {}", counts[2]);
    println!("  aborted (time or memory limit): {}", counts[3]);
    println!("  accepted, with placeholders: {}", counts[4]);
    println!("  accepted, without placeholders: {}", counts[5]);
}
