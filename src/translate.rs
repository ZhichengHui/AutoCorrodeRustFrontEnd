//! Crate-level driver: collects items, orders them, and writes the theories.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::path::Path;

use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, Ty, TyCtxt};

use crate::body::{BodyTr, Unsup};
use crate::frontend::{ExtFun, Frontend, FunDef, one_line, paren_ty};
use crate::names;

pub struct Options {
    pub out_dir: String,
    pub name: String,
    pub parent_session: String,
}

/// Tarjan's SCC algorithm; SCCs are returned callees-first.
pub fn sccs<N: Copy + Eq + std::hash::Hash>(nodes: &[N], succ: &dyn Fn(N) -> Vec<N>) -> Vec<Vec<N>> {
    struct St<N> {
        index: usize,
        idx: HashMap<N, usize>,
        low: HashMap<N, usize>,
        stack: Vec<N>,
        on: HashSet<N>,
        out: Vec<Vec<N>>,
    }
    fn go<N: Copy + Eq + std::hash::Hash>(v: N, st: &mut St<N>, succ: &dyn Fn(N) -> Vec<N>, nodes: &HashSet<N>) {
        st.idx.insert(v, st.index);
        st.low.insert(v, st.index);
        st.index += 1;
        st.stack.push(v);
        st.on.insert(v);
        for w in succ(v) {
            if !nodes.contains(&w) {
                continue;
            }
            if !st.idx.contains_key(&w) {
                go(w, st, succ, nodes);
                let lw = st.low[&w];
                let lv = st.low[&v];
                st.low.insert(v, lv.min(lw));
            } else if st.on.contains(&w) {
                let iw = st.idx[&w];
                let lv = st.low[&v];
                st.low.insert(v, lv.min(iw));
            }
        }
        if st.low[&v] == st.idx[&v] {
            let mut comp = vec![];
            loop {
                let w = st.stack.pop().unwrap();
                st.on.remove(&w);
                comp.push(w);
                if w == v {
                    break;
                }
            }
            comp.reverse();
            st.out.push(comp);
        }
    }
    let set: HashSet<N> = nodes.iter().copied().collect();
    let mut st = St { index: 0, idx: HashMap::new(), low: HashMap::new(), stack: vec![], on: HashSet::new(), out: vec![] };
    for &n in nodes {
        if !st.idx.contains_key(&n) {
            go(n, &mut st, succ, &set);
        }
    }
    st.out
}

pub fn run<'tcx>(tcx: TyCtxt<'tcx>, opts: &Options) {
    let mut fe = Frontend::new(tcx, opts.name.clone());
    let items = tcx.hir_crate_items(());

    // ---------------- types ----------------
    let mut adts: Vec<DefId> = vec![];
    for id in items.free_items() {
        let item = tcx.hir_item(id);
        let did = item.owner_id.to_def_id();
        match item.kind {
            hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => adts.push(did),
            hir::ItemKind::Union(..) => {
                fe.item_comments.push(format!(
                    "PLACEHOLDER: union `{}` is not supported (declared as an abstract type)",
                    tcx.item_name(did)
                ));
                fe.note_placeholder("union", item.span);
            }
            _ => {}
        }
    }
    // type dependency graph
    let adt_set: HashSet<DefId> = adts.iter().copied().collect();
    let deps = |did: DefId| -> Vec<DefId> {
        let mut out = vec![];
        for f in tcx.adt_def(did).all_fields() {
            let t = tcx.type_of(f.did).instantiate_identity().skip_normalization();
            for g in t.walk() {
                if let ty::GenericArgKind::Type(tt) = g.kind() {
                    if let ty::Adt(d, _) = tt.kind() {
                        if adt_set.contains(&d.did()) {
                            out.push(d.did())
                        }
                    }
                }
            }
        }
        out
    };
    let adt_sccs = sccs(&adts, &deps);
    for comp in &adt_sccs {
        let recursive = comp.len() > 1 || deps(comp[0]).contains(&comp[0]);
        for &d in comp {
            let def = tcx.adt_def(d);
            if def.is_struct() && !recursive && !def.non_enum_variant().fields.is_empty() {
                fe.record_adts.insert(d);
            }
        }
    }
    fe.adts = adts.clone();
    for &d in &adts {
        fe.adt_name(d);
    }
    let types_text = emit_types(&mut fe, &adt_sccs);

    // ---------------- functions / consts ----------------
    let mut bodies: Vec<(DefId, &'static str)> = vec![];
    for id in items.free_items() {
        let item = tcx.hir_item(id);
        let did = item.owner_id.to_def_id();
        match item.kind {
            hir::ItemKind::Fn { .. } => bodies.push((did, "fn")),
            hir::ItemKind::Const(..) => bodies.push((did, "const")),
            hir::ItemKind::Static(m, ..) => {
                if m.is_mut() {
                    fe.item_comments.push(format!("PLACEHOLDER: `static mut {}` is not supported", tcx.item_name(did)));
                    fe.note_placeholder("static mut", item.span);
                } else {
                    bodies.push((did, "static"));
                }
            }
            hir::ItemKind::Trait { ident, .. } => {
                fe.item_comments.push(format!(
                    "PLACEHOLDER: trait `{}` -- trait definitions are not translated; their implementations are translated as ordinary functions",
                    ident
                ));
                fe.note_placeholder("trait definition", item.span);
            }
            hir::ItemKind::TraitAlias(..) => {
                fe.item_comments.push("PLACEHOLDER: trait alias".into());
                fe.note_placeholder("trait alias", item.span);
            }
            hir::ItemKind::GlobalAsm { .. } => {
                fe.item_comments.push("PLACEHOLDER: global_asm! is not supported".into());
                fe.note_placeholder("global assembly", item.span);
            }
            hir::ItemKind::Impl(_) => {
                if tcx.is_automatically_derived(did) {
                    continue;
                }
                if let Some(tr) = tcx.impl_opt_trait_ref(did) {
                    if tcx.item_name(tr.skip_binder().def_id).as_str() == "Drop" {
                        fe.item_comments.push(format!(
                            "NOTE: `impl Drop for {}`: `drop` is translated as an ordinary function; destructor calls are not inserted",
                            fe.short_ty_name(tcx.type_of(did).instantiate_identity().skip_normalization())
                        ));
                        fe.note_placeholder("destructor (Drop) semantics", item.span);
                    }
                }
            }
            hir::ItemKind::ForeignMod { items: fitems, .. } => {
                for fi in fitems.iter() {
                    let fdid = fi.owner_id.to_def_id();
                    if matches!(tcx.def_kind(fdid), DefKind::Fn) {
                        fe.ext_fun(fdid, true);
                    } else {
                        fe.item_comments.push(format!("PLACEHOLDER: foreign static `{}`", tcx.item_name(fdid)));
                        fe.note_placeholder("foreign static", tcx.def_span(fdid));
                    }
                }
            }
            _ => {}
        }
    }
    for id in items.impl_items() {
        let ii = tcx.hir_impl_item(id);
        let did = ii.owner_id.to_def_id();
        let imp = tcx.parent(did);
        if tcx.is_automatically_derived(imp) {
            continue;
        }
        match ii.kind {
            hir::ImplItemKind::Fn(..) => bodies.push((did, "fn")),
            hir::ImplItemKind::Const(..) => bodies.push((did, "const")),
            hir::ImplItemKind::Type(..) => {
                fe.item_comments.push(format!("PLACEHOLDER: associated type `{}` is not supported", ii.ident));
                fe.note_placeholder("associated type", ii.span);
            }
        }
    }
    for id in items.trait_items() {
        let ti = tcx.hir_trait_item(id);
        match ti.kind {
            hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(_)) => {
                fe.item_comments.push(format!("PLACEHOLDER: default method `{}` of a trait is not translated", ti.ident));
                fe.note_placeholder("trait default method", ti.span);
            }
            hir::TraitItemKind::Type(..) => {
                fe.item_comments.push(format!("PLACEHOLDER: associated type `{}` of a trait is not supported", ti.ident));
                fe.note_placeholder("associated type", ti.span);
            }
            _ => {}
        }
    }
    for (d, _) in &bodies {
        fe.def_name(*d);
    }
    for (did, kind) in &bodies {
        let fd = translate_item(&mut fe, *did, kind);
        fe.fun_defs.push(fd);
    }

    let funs_text = emit_funs(&mut fe);
    write_all(&mut fe, opts, types_text, funs_text);
}

fn translate_item<'tcx>(fe: &mut Frontend<'tcx>, did: DefId, kind: &str) -> FunDef {
    let tcx = fe.tcx;
    let ld: LocalDefId = did.expect_local();
    let name = fe.def_name(did);
    let rust_path = tcx.def_path_str(did);
    let (param_tys, ret_ty): (Vec<String>, String) = if kind == "fn" {
        let sig = tcx.fn_sig(did).instantiate_identity().skip_binder();
        let ins: Vec<Ty<'tcx>> = sig.inputs().iter().copied().collect();
        (ins.iter().map(|t| fe.ty(*t)).collect(), fe.ty(sig.output()))
    } else {
        (vec![], fe.ty(tcx.type_of(did).instantiate_identity().skip_normalization()))
    };
    let mut fd = FunDef {
        def_id: did,
        name,
        rust_path,
        param_tys,
        ret_ty,
        params: vec![],
        body: String::new(),
        calls: crate::frontend::DefSet::default(),
        comments: vec![],
    };
    let sp = tcx.def_span(did);
    let fn_placeholder = |fe: &mut Frontend<'tcx>, fd: &mut FunDef, msg: &str| {
        fe.note_placeholder(msg, sp);
        fd.params = (0..fd.param_tys.len()).map(|i| format!("arg_{}", i)).collect();
        fd.body = format!(
            "unimplemented!(\"{}\")",
            names::string_token(&format!("UNSUPPORTED {}: {}", msg, fd.rust_path))
        );
        fd.calls.clear();
        fd.comments.push(format!("PLACEHOLDER: {}", msg));
    };
    if kind == "fn" && tcx.asyncness(did).is_async() {
        fn_placeholder(fe, &mut fd, "async fn");
        return fd;
    }
    if tcx.generics_of(did).own_params.iter().any(|p| matches!(p.kind, ty::GenericParamDefKind::Const { .. })) {
        fn_placeholder(fe, &mut fd, "const generic parameter");
        return fd;
    }
    if fd.ret_ty.contains("unsupported_") {
        // no uRust value of a placeholder type can be produced
        let msg = format!("result type `{}`", tcx.fn_sig(did).instantiate_identity().skip_binder().output());
        let msg = if kind == "fn" { msg } else { "type of constant".to_string() };
        fn_placeholder(fe, &mut fd, &msg);
        return fd;
    }
    if tcx.hir_maybe_body_owned_by(ld).is_none() {
        fn_placeholder(fe, &mut fd, "item without body");
        return fd;
    }
    let body = tcx.hir_body_owned_by(ld);
    let mut bt = BodyTr::new(fe, ld);
    let res = bt.fn_body(body);
    let calls = std::mem::take(&mut bt.calls);
    let comments = std::mem::take(&mut bt.comments);
    match res {
        Ok((params, text)) => {
            fd.params = params;
            fd.body = text;
            fd.calls = calls;
            fd.comments = comments;
        }
        Err(Unsup(m)) => fn_placeholder(fe, &mut fd, &m),
    }
    fd
}

// ----------------------------------------------------------------------
// Emission
// ----------------------------------------------------------------------

fn cart(s: &str) -> String {
    format!("\\<open>{}\\<close>", s)
}

fn emit_types<'tcx>(fe: &mut Frontend<'tcx>, adt_sccs: &[Vec<DefId>]) -> String {
    let tcx = fe.tcx;
    let mut out = String::new();
    for comp in adt_sccs {
        let mut decls = vec![];
        let mut after = String::new();
        for &d in comp {
            let def = tcx.adt_def(d);
            let tn = fe.adt_name(d);
            let generics = tcx.generics_of(d);
            let tparams: Vec<String> = generics
                .own_params
                .iter()
                .filter(|p| matches!(p.kind, ty::GenericParamDefKind::Type { .. }))
                .map(|p| names::tvar_name(p.name.as_str()))
                .collect();
            let has_const = generics.own_params.iter().any(|p| matches!(p.kind, ty::GenericParamDefKind::Const { .. }));
            let head = if tparams.is_empty() { tn.clone() } else { format!("({}) {}", tparams.join(", "), tn) };
            writeln!(out, "(* Rust: {} *)", tcx.def_path_str(d)).unwrap();
            if has_const {
                writeln!(out, "(* PLACEHOLDER: const generic parameters are not supported *)").unwrap();
                fe.note_placeholder("const generic parameter", tcx.def_span(d));
            }
            if def.is_enum() && def.variants().is_empty() {
                writeln!(out, "(* PLACEHOLDER: empty enum *)\ntypedecl {}\n", head).unwrap();
                fe.note_placeholder("empty enum", tcx.def_span(d));
                continue;
            }
            if def.is_enum() && def.variants().iter().any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_))) {
                writeln!(out, "(* PLACEHOLDER: explicit discriminant values are dropped *)").unwrap();
                fe.note_placeholder("enum with explicit discriminants", tcx.def_span(d));
            }
            if def.is_struct() {
                let v = def.non_enum_variant();
                let ftys: Vec<String> =
                    v.fields.iter().map(|f| fe.ty(tcx.type_of(f.did).instantiate_identity().skip_normalization())).collect();
                let fnames: Vec<String> = (0..v.fields.len()).map(|k| fe.field_name(d, 0, k)).collect();
                if v.fields.is_empty() {
                    decls.push(format!("{} = make_{}", head, tn));
                } else if fe.record_adts.contains(&d) {
                    let mut s = format!("datatype_record {} =\n", head);
                    for (n, t) in fnames.iter().zip(ftys.iter()) {
                        writeln!(s, "  {} :: {}", n, cart(t)).unwrap();
                    }
                    writeln!(s, "micro_rust_record {}\n", tn).unwrap();
                    out.push_str(&s);
                } else {
                    let args: Vec<String> =
                        fnames.iter().zip(ftys.iter()).map(|(n, t)| format!("({}: {})", n, cart(t))).collect();
                    decls.push(format!("{} = make_{} {}", head, tn, args.join(" ")));
                }
                if !v.fields.is_empty() {
                    after.push_str(&ctor_fun(&format!("{}_mk", tn), &format!("make_{}", tn), &ftys, &head, &tn));
                }
            } else {
                let mut ctors = vec![];
                for (vi, v) in def.variants().iter().enumerate() {
                    let cn = fe.variant_ctor_name(d, vi);
                    let ftys: Vec<String> =
                        v.fields.iter().map(|f| fe.ty(tcx.type_of(f.did).instantiate_identity().skip_normalization())).collect();
                    let args: Vec<String> = ftys.iter().map(|t| cart(t)).collect();
                    ctors.push(if args.is_empty() { cn.clone() } else { format!("{} {}", cn, args.join(" ")) });
                    if !ftys.is_empty() {
                        after.push_str(&ctor_fun(&format!("{}_mk", cn), &cn, &ftys, &head, &cn));
                    }
                }
                decls.push(format!("{} =\n    {}", head, ctors.join("\n  | ")));
            }
        }
        if !decls.is_empty() {
            writeln!(out, "datatype {}\n", decls.join("\nand ")).unwrap();
        }
        out.push_str(&after);
    }
    out
}

/// Constructor function `NAME = (λa0 .. an. FunctionBody (literal (CTOR a0 .. an)))`,
/// registered as the uRust callable `urust_name`.
fn ctor_fun(name: &str, ctor: &str, ftys: &[String], self_ty: &str, urust_name: &str) -> String {
    let ps: Vec<String> = (0..ftys.len()).map(|i| format!("a{}", i)).collect();
    let mut ty = String::new();
    for t in ftys {
        ty.push_str(&paren_ty(t));
        ty.push_str(" \\<Rightarrow> ");
    }
    ty.push_str(&format!("('s, {}, 'abort, 'i, 'o) function_body", self_ty));
    format!(
        "definition {} :: {} where\n  {}\nmicro_rust_notation (call) {} (\"{}\")\n\n",
        name,
        cart(&ty),
        cart(&format!(
            "{} \\<equiv> \\<lambda>{}. FunctionBody (literal ({} {}))",
            name,
            ps.join(" "),
            ctor,
            ps.join(" ")
        )),
        name,
        urust_name
    )
}

fn subst_markers(fe: &Frontend<'_>, body: &str, caller_scc: Option<&HashSet<DefId>>, names: &HashMap<DefId, String>) -> String {
    let mut out = String::new();
    let mut rest = body;
    while let Some(i) = rest.find('\u{1}') {
        out.push_str(&rest[..i]);
        let j = rest[i..].find('\u{2}').unwrap() + i;
        let tag = &rest[i + 1..j];
        let kind = &tag[..1];
        let idx: usize = tag[1..].parse().unwrap();
        let did = fe.marker_ids[idx];
        let name = names.get(&did).cloned().unwrap_or_else(|| format!("MISSING_{}", idx));
        let rec = caller_scc.map(|s| s.contains(&did)).unwrap_or(false);
        let s = match (kind, rec) {
            ("C", false) | ("H", false) => name.clone(),
            ("Z", false) => format!("{}()", name),
            ("C", true) => format!("\\<epsilon>\\<open>{}_fuel fuel_rec\\<close>", name),
            ("H", true) => format!("({}_fuel fuel_rec)", name),
            ("Z", true) => format!("\\<epsilon>\\<open>funcall0 ({}_fuel fuel_rec)\\<close>", name),
            _ => unreachable!(),
        };
        out.push_str(&s);
        rest = &rest[j + 1..];
    }
    out.push_str(rest);
    out
}

/// Re-indent generated uRust text by brace depth.
fn indent(s: &str, n: usize) -> String {
    let pad = " ".repeat(n);
    let mut depth: i32 = 0;
    let mut out = String::new();
    for line in s.lines() {
        let l = line.trim();
        if l.is_empty() {
            continue;
        }
        let opens = l.matches('{').count() as i32;
        let closes = l.matches('}').count() as i32;
        let d = if l.starts_with('}') { depth - 1 } else { depth };
        out.push_str(&pad);
        out.push_str(&"  ".repeat(d.max(0) as usize));
        out.push_str(l);
        out.push('\n');
        depth += opens - closes;
    }
    out
}

fn emit_funs(fe: &mut Frontend<'_>) -> String {
    let defs = std::mem::take(&mut fe.fun_defs);
    let ids: Vec<DefId> = defs.iter().map(|d| d.def_id).collect();
    let by_id: HashMap<DefId, usize> = defs.iter().enumerate().map(|(i, d)| (d.def_id, i)).collect();
    let names: HashMap<DefId, String> = defs.iter().map(|d| (d.def_id, d.name.clone())).collect();
    let succ = |d: DefId| -> Vec<DefId> { defs[by_id[&d]].calls.iter().copied().collect() };
    let comps = sccs(&ids, &succ);
    let mut out = String::new();
    for comp in comps {
        let recursive = comp.len() > 1 || defs[by_id[&comp[0]]].calls.contains(&comp[0]);
        if !recursive {
            let d = &defs[by_id[&comp[0]]];
            let body = subst_markers(fe, &d.body, None, &names);
            out.push_str(&emit_def(fe, d, &body));
            continue;
        }
        let set: HashSet<DefId> = comp.iter().copied().collect();
        let mut heads = vec![];
        let mut eqs = vec![];
        writeln!(
            out,
            "text \\<open>Recursive group, translated with a fuel parameter: {}\\<close>\n",
            comp.iter().map(|c| defs[by_id[c]].name.clone()).collect::<Vec<_>>().join(", ")
        )
        .unwrap();
        for c in &comp {
            let d = &defs[by_id[c]];
            let ty = fe.fun_type(&d.param_tys, &d.ret_ty);
            heads.push(format!("{}_fuel :: {}", d.name, cart(&format!("nat \\<Rightarrow> {}", ty))));
            let lam = if d.params.is_empty() { String::new() } else { format!("\\<lambda>{}. ", d.params.join(" ")) };
            let body = subst_markers(fe, &d.body, Some(&set), &names);
            eqs.push(cart(&format!(
                "{}_fuel 0 = ({}FunctionBody \\<lbrakk> panic!(\"out of fuel\") \\<rbrakk>)",
                d.name, lam
            )));
            eqs.push(cart(&format!(
                "{}_fuel (Suc fuel_rec) = ({}FunctionBody \\<lbrakk>\n{}  \\<rbrakk>)",
                d.name,
                lam,
                indent(&body, 4)
            )));
        }
        writeln!(out, "fun {} where\n  {}\n", heads.join("\nand "), eqs.join("\n| ")).unwrap();
        for c in &comp {
            let d = &defs[by_id[c]];
            writeln!(out, "(* Rust: {} *)", d.rust_path).unwrap();
            for cm in &d.comments {
                writeln!(out, "(* {} *)", cm).unwrap();
            }
            let ty = fe.fun_type(&d.param_tys, &d.ret_ty);
            writeln!(
                out,
                "definition {} :: {} where\n  {}\n",
                d.name,
                cart(&ty),
                cart(&format!("{} \\<equiv> {}_fuel urust_fuel", d.name, d.name))
            )
            .unwrap();
        }
    }
    fe.fun_defs = defs;
    out
}

fn emit_def(fe: &Frontend<'_>, d: &FunDef, body: &str) -> String {
    let mut out = String::new();
    writeln!(out, "(* Rust: {} *)", d.rust_path).unwrap();
    for c in &d.comments {
        writeln!(out, "(* {} *)", c).unwrap();
    }
    let ty = fe.fun_type(&d.param_tys, &d.ret_ty);
    let lam = if d.params.is_empty() { String::new() } else { format!("\\<lambda>{}. ", d.params.join(" ")) };
    writeln!(
        out,
        "definition {} :: {} where\n  \\<open>{} \\<equiv> {}FunctionBody \\<lbrakk>\n{}  \\<rbrakk>\\<close>\n",
        d.name,
        cart(&ty),
        d.name,
        lam,
        indent(body, 4)
    )
    .unwrap();
    out
}

fn emit_ext_funs(funs: &std::collections::BTreeMap<String, ExtFun>, what: &str) -> String {
    let mut out = String::new();
    for f in funs.values() {
        let ps: Vec<String> = (0..f.arity).map(|i| format!("a{}", i)).collect();
        let lam = if ps.is_empty() { String::new() } else { format!("\\<lambda>{}. ", ps.join(" ")) };
        writeln!(
            out,
            "(* Rust: {} *)\ndefinition {} :: {} where\n  {}\n",
            f.rust_path,
            f.hol_name,
            cart(&f.hol_type),
            cart(&format!(
                "{} \\<equiv> {}FunctionBody \\<lbrakk> unimplemented!(\"{}\") \\<rbrakk>",
                f.hol_name,
                lam,
                names::string_token(&format!("{} {}", what, f.rust_path))
            ))
        )
        .unwrap();
    }
    out
}

fn write_all(fe: &mut Frontend<'_>, opts: &Options, types_text: String, funs_text: String) {
    let c = &opts.name;
    let dir = Path::new(&opts.out_dir);
    std::fs::create_dir_all(dir).unwrap();
    let ctx = format!("{}_ctx", c);
    let header = |t: &str| format!("(* Generated by urust-frontend from crate `{}`. *)\n\ntheory {}\n", c, t);

    // external / placeholder types
    let mut te = header(&format!("{}_TypesExternal_Template", c));
    te.push_str("  imports \"Micro_Rust_Std_Lib.StdLib_All\"\nbegin\n\n");
    te.push_str("text \\<open>Types without a uRust model. Replace these declarations by models.\\<close>\n\n");
    for (n, t) in &fe.ext_types {
        let args = if t.arity == 0 {
            String::new()
        } else {
            format!("({}) ", (0..t.arity).map(|i| format!("'t{}", i)).collect::<Vec<_>>().join(", "))
        };
        writeln!(te, "(* {} *)\ntypedecl {}{}\n", t.comment, args, n).unwrap();
    }
    te.push_str("end\n");

    let mut ty = header(&format!("{}_Types", c));
    writeln!(ty, "  imports {}_TypesExternal_Template\nbegin\n", c).unwrap();
    ty.push_str(&types_text);
    ty.push_str("end\n");

    // locale
    let mut lo = header(&format!("{}_Locale", c));
    writeln!(lo, "  imports {}_Types\nbegin\n", c).unwrap();
    writeln!(
        lo,
        "text \\<open>Heap of the crate: one \\<^verbatim>\\<open>reference_allocatable\\<close> instance per type of a mutable local.\nLoops without an iteration bound and recursive functions use the fuel \\<^verbatim>\\<open>urust_fuel\\<close>.\\<close>\n"
    )
    .unwrap();
    writeln!(lo, "locale {} =\n  reference reference_types", ctx).unwrap();
    for (i, t) in fe.alloc_types.iter().enumerate() {
        writeln!(lo, "  + ref_{}: reference_allocatable reference_types _ _ _ _ _ _ _ prism_{} \\<comment> \\<open>{}\\<close>", i + 1, i + 1, t).unwrap();
    }
    writeln!(
        lo,
        "  for reference_types :: \\<open>'s::{{sepalg}} \\<Rightarrow> 'addr \\<Rightarrow> 'gv \\<Rightarrow> 'abort \\<Rightarrow> 'i prompt \\<Rightarrow> 'o prompt_output \\<Rightarrow> unit\\<close>"
    )
    .unwrap();
    for (i, t) in fe.alloc_types.iter().enumerate() {
        writeln!(lo, "  and prism_{} :: \\<open>('gv, {}) prism\\<close>", i + 1, t).unwrap();
    }
    writeln!(lo, "  + fixes urust_fuel :: nat\nbegin\n").unwrap();
    for (i, _) in fe.alloc_types.iter().enumerate() {
        writeln!(lo, "adhoc_overloading store_reference_const \\<rightleftharpoons> ref_{}.new", i + 1).unwrap();
    }
    writeln!(lo, "adhoc_overloading store_update_const \\<rightleftharpoons> update_fun\n\nend\n\nend").unwrap();

    let mut fx = header(&format!("{}_FunsExternal_Template", c));
    writeln!(
        fx,
        "  imports {}_Locale\nbegin\n\ntext \\<open>Functions without a definition in this crate. Replace the bodies by uRust models.\\<close>\n\ncontext {}\nbegin\n",
        c, ctx
    )
    .unwrap();
    fx.push_str(&emit_ext_funs(&fe.ext_funs, "external function"));
    fx.push_str("end\n\nend\n");

    let mut ff = header(&format!("{}_FunsForeign_Template", c));
    writeln!(
        ff,
        "  imports {}_Locale\nbegin\n\ntext \\<open>Functions declared in \\<^verbatim>\\<open>extern\\<close> blocks. They cannot be replaced by uRust models; their contracts must also state memory effects.\\<close>\n\ncontext {}\nbegin\n",
        c, ctx
    )
    .unwrap();
    ff.push_str(&emit_ext_funs(&fe.foreign_funs, "foreign function"));
    ff.push_str("end\n\nend\n");

    let mut fu = header(&format!("{}_Funs", c));
    writeln!(fu, "  imports {}_FunsExternal_Template {}_FunsForeign_Template\nbegin\n\ncontext {}\nbegin\n", c, c, ctx).unwrap();
    for cmt in &fe.item_comments {
        writeln!(fu, "(* {} *)", cmt).unwrap();
    }
    if !fe.item_comments.is_empty() {
        fu.push('\n');
    }
    fu.push_str(&funs_text);
    fu.push_str("end\n\nend\n");

    let files = [
        (format!("{}_TypesExternal_Template.thy", c), te),
        (format!("{}_Types.thy", c), ty),
        (format!("{}_Locale.thy", c), lo),
        (format!("{}_FunsExternal_Template.thy", c), fx),
        (format!("{}_FunsForeign_Template.thy", c), ff),
        (format!("{}_Funs.thy", c), fu),
    ];
    for (n, t) in files.iter() {
        std::fs::write(dir.join(n), t).unwrap();
    }
    let root = format!(
        "session \"{}\" = \"{}\" +\n  options [document = false]\n  theories\n    {}_Funs\n",
        c, opts.parent_session, c
    );
    std::fs::write(dir.join("ROOT"), root).unwrap();
    let mut rep = format!("Placeholders for unsupported features in crate `{}`: {}\n", c, fe.placeholders.len());
    for p in &fe.placeholders {
        writeln!(rep, "- {}", one_line(p)).unwrap();
    }
    std::fs::write(dir.join("PLACEHOLDERS.txt"), &rep).unwrap();
    eprint!("{}", rep);
}
