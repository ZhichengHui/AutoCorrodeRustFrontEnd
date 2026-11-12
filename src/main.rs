//! urust-frontend: translate the HIR of a Rust library crate into AutoCorrode uRust theories.
//!
//! Usage:
//!   urust-frontend [--out DIR] [--name NAME] [--parent SESSION] FILE.rs [-- RUSTC-ARGS...]

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_arena;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_pattern_analysis;
extern crate rustc_span;

mod body;
mod dict;
mod frontend;
mod names;
mod reachability;
mod translate;

use rustc_driver::Compilation;
use rustc_middle::ty::TyCtxt;

struct Callbacks {
    opts: translate::Options,
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_, providers| reachability::wrap_check_match(providers));
    }

    fn after_analysis<'tcx>(&mut self, _c: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        translate::run(tcx, &self.opts);
        Compilation::Stop
    }
}

fn usage() -> ! {
    eprintln!("usage: urust-frontend [--out DIR] [--name NAME] [--parent SESSION] FILE.rs [-- RUSTC-ARGS...]");
    std::process::exit(2)
}

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mut out = None;
    let mut name = None;
    let mut parent = "AutoCorrode".to_string();
    let mut file = None;
    let mut extra = vec![];
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--out" => { i += 1; out = Some(args.get(i).cloned().unwrap_or_else(|| usage())); }
            "--name" => { i += 1; name = Some(args.get(i).cloned().unwrap_or_else(|| usage())); }
            "--parent" => { i += 1; parent = args.get(i).cloned().unwrap_or_else(|| usage()); }
            "--" => { extra.extend(args[i + 1..].iter().cloned()); break; }
            "-h" | "--help" => usage(),
            a => {
                if file.is_some() { usage() }
                file = Some(a.to_string());
            }
        }
        i += 1;
    }
    let Some(file) = file else { usage() };
    let stem = std::path::Path::new(&file).file_stem().unwrap().to_string_lossy().to_string();
    let name = name.unwrap_or_else(|| names::ident_chars(&stem));
    let out = out.unwrap_or_else(|| format!("out/{}", name));
    let mut rustc_args = vec![
        args[0].clone(),
        file.clone(),
        "--crate-type=lib".to_string(),
        "-Awarnings".to_string(),
        format!("--crate-name={}", names::ident_chars(&stem).to_lowercase()),
    ];
    if !extra.iter().any(|a| a.starts_with("--edition")) {
        rustc_args.push("--edition=2024".to_string());
    }
    rustc_args.extend(extra);
    let mut cb = Callbacks { opts: translate::Options { out_dir: out, name, parent_session: parent } };
    rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&rustc_args, &mut cb))
}
