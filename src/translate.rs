//! Crate-level driver: collects items, orders them, and writes the theories.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::path::Path;

use rustc_hir as hir;
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};

use crate::body::{BodyTr, Unsup};
use crate::frontend::{ExtFun, FnKey, Frontend, FunDef, one_line, paren_ty};
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
    let mut fe = Frontend::new(tcx);
    let items = tcx.hir_crate_items(());

    // ---------------- types ----------------
    let mut adts: Vec<DefId> = vec![];
    for id in items.free_items() {
        let item = tcx.hir_item(id);
        let did = item.owner_id.to_def_id();
        match item.kind {
            hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => adts.push(did),
            hir::ItemKind::Union(..) => {
                let m = fe.placeholder("union (declared as an abstract type)", Some(tcx.def_span(did)));
                fe.item_comments.push(m);
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
    // a HOL datatype recurs with its own type parameters, in order: a group of ADTs recurring with
    // other type arguments is a placeholder
    for comp in &adt_sccs {
        let nonuniform = comp.iter().any(|&d| {
            tcx.adt_def(d).all_fields().any(|f| {
                tcx.type_of(f.did).instantiate_identity().skip_normalization().walk().any(|g| match g.kind() {
                    ty::GenericArgKind::Type(tt) => match tt.kind() {
                        ty::Adt(e, args) if comp.contains(&e.did()) => {
                            let own = ty::GenericArgs::identity_for_item(tcx, e.did());
                            args.types().collect::<Vec<_>>() != own.types().collect::<Vec<_>>()
                        }
                        _ => false,
                    },
                    _ => false,
                })
            })
        });
        if nonuniform {
            for &d in comp {
                fe.opaque_adts.insert(d, "non-uniformly recursive");
                let m = fe.placeholder("non-uniformly recursive type (declared as an abstract type)", Some(tcx.def_span(d)));
                fe.item_comments.push(m);
            }
        }
    }
    // a shared reference `&T` is a value of `T`, so a type whose every value contains a value of
    // the same type through shared references (e.g. `struct Node(&'static Node)`, whose values are
    // cycles of statics) has no finite values, and its HOL datatype (a least fixpoint) is empty.
    // Least fixpoint of the ADTs with finite values; abstract types (`typedecl`) are not empty.
    let mut finite: HashSet<DefId> = adts
        .iter()
        .copied()
        .filter(|d| fe.opaque_adts.contains_key(d) || (tcx.adt_def(*d).is_enum() && tcx.adt_def(*d).variants().is_empty()))
        .collect();
    loop {
        let mut changed = false;
        for &d in &adts {
            if finite.contains(&d) { continue }
            let has_finite_value = tcx.adt_def(d).variants().iter().any(|v| {
                v.fields.iter().all(|f| fe.finite_ty(tcx.type_of(f.did).instantiate_identity().skip_normalization(), &adt_set, &finite))
            });
            if has_finite_value {
                finite.insert(d);
                changed = true;
            }
        }
        if !changed { break }
    }
    for comp in &adt_sccs {
        if comp.iter().all(|d| finite.contains(d)) { continue }
        for &d in comp {
            fe.opaque_adts.insert(d, "without finite values");
            let m = fe.placeholder(
                "type without finite values when shared references are values, or recursive with one (declared as an abstract type)",
                Some(tcx.def_span(d)),
            );
            fe.item_comments.push(m);
        }
    }
    for comp in &adt_sccs {
        let recursive = comp.len() > 1 || deps(comp[0]).contains(&comp[0]);
        for &d in comp {
            let def = tcx.adt_def(d);
            if def.is_struct() && !recursive && !def.non_enum_variant().fields.is_empty() {
                fe.record_adts.insert(d);
            }
        }
    }
    // ADTs containing `&mut` references, directly or through other local ADTs
    loop {
        let mut changed = false;
        for &d in &adts {
            if fe.ref_adts.contains(&d) {
                continue;
            }
            let needs = tcx.adt_def(d).all_fields().any(|f| {
                tcx.type_of(f.did).instantiate_identity().skip_normalization().walk().any(|g| match g.kind() {
                    ty::GenericArgKind::Type(tt) => match tt.kind() {
                        ty::Ref(_, _, m) => m.is_mut(),
                        ty::Adt(a, _) => fe.ref_adts.contains(&a.did()),
                        _ => false,
                    },
                    _ => false,
                })
            });
            if needs {
                fe.ref_adts.insert(d);
                changed = true;
            }
        }
        if !changed {
            break;
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
            hir::ItemKind::Fn { .. } if !fe.bodiless_intrinsic(did) => bodies.push((did, "fn")),
            hir::ItemKind::Const(..) => bodies.push((did, "const")),
            hir::ItemKind::Static(m, ..) => {
                if m.is_mut() {
                    let m = fe.placeholder("static mut", Some(tcx.def_span(did)));
                    fe.item_comments.push(m);
                } else {
                    bodies.push((did, "static"));
                }
            }
            hir::ItemKind::Trait { .. } => {
                let m = fe.placeholder(
                    "trait definition (its implementations are translated as ordinary functions)",
                    Some(tcx.def_span(did)),
                );
                fe.item_comments.push(m);
            }
            hir::ItemKind::TraitAlias(..) => {
                let m = fe.placeholder("trait alias", Some(tcx.def_span(did)));
                fe.item_comments.push(m);
            }
            hir::ItemKind::GlobalAsm { .. } => {
                let m = fe.placeholder("global assembly", Some(item.span));
                fe.item_comments.push(m);
            }
            hir::ItemKind::Impl(_) => {
                if tcx.is_automatically_derived(did) {
                    continue;
                }
                if let Some(tr) = tcx.impl_opt_trait_ref(did) {
                    if tcx.is_lang_item(tr.skip_binder().def_id, LangItem::Drop) {
                        let m = fe.placeholder(
                            "destructor semantics (drop is translated as an ordinary function; destructor calls are not inserted)",
                            Some(tcx.def_span(did)),
                        );
                        fe.item_comments.push(m);
                    }
                }
            }
            hir::ItemKind::ForeignMod { items: fitems, .. } => {
                for fi in fitems.iter() {
                    let fdid = fi.owner_id.to_def_id();
                    if matches!(tcx.def_kind(fdid), DefKind::Fn) {
                        fe.ext_fun(fdid, true);
                    } else {
                        let m = fe.placeholder("foreign static", Some(tcx.def_span(fdid)));
                        fe.item_comments.push(m);
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
                let m = fe.placeholder("associated type", Some(tcx.def_span(did)));
                fe.item_comments.push(m);
            }
        }
    }
    // default methods are generic over `Self`: translated at the instances they are called at
    let mut default_methods: Vec<DefId> = vec![];
    for id in items.trait_items() {
        let ti = tcx.hir_trait_item(id);
        match ti.kind {
            hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(_)) => default_methods.push(ti.owner_id.to_def_id()),
            hir::TraitItemKind::Type(..) => {
                let m = fe.placeholder("associated type", Some(tcx.def_span(ti.owner_id.to_def_id())));
                fe.item_comments.push(m);
            }
            _ => {}
        }
    }
    fe.mono_fns = mono_fns(tcx, &bodies, &default_methods);
    for (d, _) in &bodies {
        fe.def_name(*d);
    }
    for (did, kind) in &bodies {
        let fd = translate_item(&mut fe, (*did, None), kind);
        fe.fun_defs.push(fd);
    }
    // instances called from the translated bodies, and from those instances
    while let Some(key) = fe.pending.pop() {
        let fd = translate_item(&mut fe, key, "fn");
        fe.fun_defs.push(fd);
    }
    for d in default_methods {
        if !fe.fun_defs.iter().any(|f| f.key.0 == d) {
            let m = fe.placeholder("trait default method (not called at a concrete type)", Some(tcx.def_span(d)));
            fe.item_comments.push(m);
        }
    }

    let funs_text = emit_funs(&mut fe);
    write_all(&mut fe, opts, types_text, funs_text);
}

/// The calls of a body whose callee depends on the body's generic parameters: trait methods and
/// generic `Fn` values (`dependent`), and local functions at such arguments (`callees`).
struct GenericCalls<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    dependent: bool,
    callees: Vec<DefId>,
}

impl<'tcx> GenericCalls<'tcx> {
    fn call(&mut self, did: DefId, args: ty::GenericArgsRef<'tcx>) {
        if !args.has_param() {
            return;
        }
        if self.tcx.trait_of_assoc(did).is_some() {
            self.dependent = true;
        } else if did.is_local() {
            self.callees.push(did);
        }
    }
}

impl<'tcx> Visitor<'tcx> for GenericCalls<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx hir::Expr<'tcx>) {
        if let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) {
            self.call(did, self.typeck.node_args(e.hir_id));
        }
        if let hir::ExprKind::Call(callee, _) = e.kind {
            let mut t = self.typeck.expr_ty_adjusted(callee);
            while let ty::Ref(_, inner, _) = t.kind() {
                t = *inner;
            }
            match *t.kind() {
                ty::FnDef(did, args) => self.call(did, args.skip_binder()),
                ty::Param(_) => self.dependent = true,
                _ => {}
            }
        }
        intravisit::walk_expr(self, e);
    }
}

/// The generic functions translated per instance: trait default methods, and generic functions
/// with a call depending on their generic parameters, directly or through other such functions.
fn mono_fns<'tcx>(tcx: TyCtxt<'tcx>, bodies: &[(DefId, &str)], default_methods: &[DefId]) -> HashSet<DefId> {
    let mut mono: HashSet<DefId> = default_methods.iter().copied().collect();
    let mut callees: Vec<(DefId, Vec<DefId>)> = vec![];
    for &(did, kind) in bodies {
        let Some(ld) = did.as_local() else { continue };
        if kind != "fn" || tcx.hir_maybe_body_owned_by(ld).is_none() {
            continue;
        }
        let mut v = GenericCalls { tcx, typeck: tcx.typeck(ld), dependent: false, callees: vec![] };
        v.visit_body(tcx.hir_body_owned_by(ld));
        if v.dependent {
            mono.insert(did);
        }
        callees.push((did, v.callees));
    }
    loop {
        let before = mono.len();
        for (did, cs) in &callees {
            if cs.iter().any(|c| mono.contains(c)) {
                mono.insert(*did);
            }
        }
        if mono.len() == before {
            return mono;
        }
    }
}

fn translate_item<'tcx>(fe: &mut Frontend<'tcx>, key: FnKey<'tcx>, kind: &str) -> FunDef<'tcx> {
    let tcx = fe.tcx;
    let did = key.0;
    let ld: LocalDefId = did.expect_local();
    let name = fe.fn_name(key);
    let rust_path = match key.1 {
        None => tcx.def_path_str(did),
        Some(args) => tcx.def_path_str_with_args(did, args),
    };
    let (params, ret): (Vec<(String, bool)>, (String, bool)) = if kind == "fn" {
        let sig = tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(did).instantiate_identity().skip_normalization());
        // an instance's types at its arguments; a generic item's projections normalised in its own
        // typing environment (e.g. `<Iter<T> as Iterator>::Item` through the impl)
        let at = |t: Ty<'tcx>| match key.1 {
            Some(args) => fe.mono(args, t),
            None => tcx
                .try_normalize_erasing_regions(ty::TypingEnv::post_analysis(tcx, did), ty::Unnormalized::new_wip(t))
                .unwrap_or(t),
        };
        let ins: Vec<Ty<'tcx>> = sig.inputs().iter().map(|t| at(*t)).collect();
        let out = at(sig.output());
        (ins.iter().map(|t| fe.ty_modelled(*t)).collect(), fe.ty_modelled(out))
    } else {
        (vec![], fe.ty_modelled(tcx.type_of(did).instantiate_identity().skip_normalization()))
    };
    let unmodelled_param = params.iter().find(|(_, m)| !m).map(|(p, _)| p.clone());
    let param_tys: Vec<String> = params.into_iter().map(|(p, _)| p).collect();
    let (ret_ty, ret_modelled) = ret;
    let mut fd = FunDef {
        key,
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
    let fn_placeholder = |fe: &mut Frontend<'tcx>, fd: &mut FunDef<'tcx>, msg: &str| {
        let m = fe.placeholder(msg, Some(sp));
        fd.params = (0..fd.param_tys.len()).map(|i| format!("arg_{}", i)).collect();
        fd.body = format!("unimplemented!(\"{}\")", names::string_token(&m));
        fd.calls.clear();
        fd.comments.push(m);
    };
    if kind == "fn" && tcx.asyncness(did).is_async() {
        fn_placeholder(fe, &mut fd, "async fn");
        return fd;
    }
    if tcx.generics_of(did).own_params.iter().any(|p| matches!(p.kind, ty::GenericParamDefKind::Const { .. })) {
        fn_placeholder(fe, &mut fd, "const generic parameter");
        return fd;
    }
    // A function whose signature mentions a type without a uRust model is a placeholder as a
    // whole.
    if let Some(p) = unmodelled_param {
        let msg = format!("parameter of unsupported type `{}`", p);
        fn_placeholder(fe, &mut fd, &msg);
        return fd;
    }
    if !ret_modelled {
        let msg = if kind == "fn" {
            format!("result type `{}`", tcx.fn_sig(did).instantiate_identity().skip_binder().output())
        } else {
            format!("type `{}` of a constant", tcx.type_of(did).instantiate_identity().skip_normalization())
        };
        fn_placeholder(fe, &mut fd, &msg);
        return fd;
    }
    if tcx.hir_maybe_body_owned_by(ld).is_none() {
        fn_placeholder(fe, &mut fd, "item without body");
        return fd;
    }
    let body = tcx.hir_body_owned_by(ld);
    let mut bt = BodyTr::new(fe, ld, key.1);
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

/// Text inside an Isabelle comment `(* .. *)`: comments nest, so `(*` and `*)` are broken up.
fn cmt(s: &str) -> String {
    s.replace("(*", "( *").replace("*)", "* )")
}

fn cart(s: &str) -> String {
    format!("\\<open>{}\\<close>", s)
}

fn emit_types<'tcx>(fe: &mut Frontend<'tcx>, adt_sccs: &[Vec<DefId>]) -> String {
    let tcx = fe.tcx;
    let mut out = String::new();
    for comp in adt_sccs {
        if comp.iter().any(|d| fe.opaque_adts.contains_key(d)) {
            continue;
        }
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
            let mut tparams = tparams;
            if fe.ref_adts.contains(&d) {
                tparams.insert(0, "'gv".into());
                tparams.insert(0, "'addr".into());
            }
            let head = if tparams.is_empty() { tn.clone() } else { format!("({}) {}", tparams.join(", "), tn) };
            writeln!(out, "(* Rust: {} *)", cmt(&tcx.def_path_str(d))).unwrap();
            if has_const {
                let m = fe.placeholder("const generic parameter", Some(tcx.def_span(d)));
                writeln!(out, "(* {} *)", cmt(&m)).unwrap();
            }
            if def.is_enum() && def.variants().is_empty() {
                let m = fe.placeholder("empty enum (declared as an abstract type)", Some(tcx.def_span(d)));
                writeln!(out, "(* {} *)\ntypedecl {}\n", cmt(&m), head).unwrap();
                continue;
            }
            if def.is_enum() && def.variants().iter().any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_))) {
                let m = fe.placeholder("explicit enum discriminants (dropped)", Some(tcx.def_span(d)));
                writeln!(out, "(* {} *)", cmt(&m)).unwrap();
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
                    after.push_str(&ctor_fun(&format!("{}_mk", tn), &format!("make_{}", tn), &ftys, &head));
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
                        after.push_str(&ctor_fun(&format!("{}_mk", cn), &cn, &ftys, &head));
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

/// Constructor function `NAME = (λa0 .. an. FunctionBody (literal (CTOR a0 .. an)))`.
/// It is called by its HOL name, because uRust notations are global and a Rust name may
/// already denote other backends.
fn ctor_fun(name: &str, ctor: &str, ftys: &[String], self_ty: &str) -> String {
    let ps: Vec<String> = (0..ftys.len()).map(|i| format!("a{}", i)).collect();
    let mut ty = String::new();
    for t in ftys {
        ty.push_str(&paren_ty(t));
        ty.push_str(" \\<Rightarrow> ");
    }
    ty.push_str(&format!("('s, {}, 'abort, 'i, 'o) function_body", self_ty));
    format!(
        "definition \"{}\" :: {} where\n  {}\n\n",
        name,
        cart(&ty),
        cart(&format!(
            "{} \\<equiv> \\<lambda>{}. FunctionBody (literal ({} {}))",
            name,
            ps.join(" "),
            ctor,
            ps.join(" ")
        ))
    )
}

fn subst_markers<'tcx>(fe: &Frontend<'tcx>, body: &str, caller_scc: Option<&HashSet<FnKey<'tcx>>>, names: &HashMap<FnKey<'tcx>, String>) -> String {
    let mut out = String::new();
    let mut rest = body;
    while let Some(i) = rest.find('\u{1}') {
        out.push_str(&rest[..i]);
        let j = rest[i..].find('\u{2}').unwrap() + i;
        let tag = &rest[i + 1..j];
        let kind = &tag[..1];
        let idx: usize = tag[1..].parse().unwrap();
        let key = fe.marker_ids[idx];
        // every marked callee is a local item with a body, hence translated
        let name = names.get(&key).cloned().expect("callee of a call marker is translated");
        let rec = caller_scc.map(|s| s.contains(&key)).unwrap_or(false);
        let s = match (kind, rec) {
            ("C", false) | ("H", false) => name.clone(),
            ("Z", false) => format!("{}()", name),
            ("C", true) => format!("\\<epsilon>\\<open>rec_{}\\<close>", name),
            ("H", true) => format!("rec_{}", name),
            ("Z", true) => format!("\\<epsilon>\\<open>funcall0 rec_{}\\<close>", name),
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

fn emit_funs<'tcx>(fe: &mut Frontend<'tcx>) -> String {
    let defs = std::mem::take(&mut fe.fun_defs);
    let ids: Vec<FnKey<'tcx>> = defs.iter().map(|d| d.key).collect();
    let by_id: HashMap<FnKey<'tcx>, usize> = defs.iter().enumerate().map(|(i, d)| (d.key, i)).collect();
    let names: HashMap<FnKey<'tcx>, String> = defs.iter().map(|d| (d.key, d.name.clone())).collect();
    let succ = |d: FnKey<'tcx>| -> Vec<FnKey<'tcx>> { defs[by_id[&d]].calls.iter().copied().collect() };
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
        // A recursive group f1..fk is defined by iterating a non-recursive step functional
        // `urust_fuel` times, starting from functions that panic ("out of fuel").
        let set: HashSet<FnKey<'_>> = comp.iter().copied().collect();
        let members: Vec<&FunDef<'_>> = comp.iter().map(|c| &defs[by_id[c]]).collect();
        let k = members.len();
        let step = format!("{}_rec_step", members[0].name);
        let tys: Vec<String> = members.iter().map(|d| fe.fun_type(&d.param_tys, &d.ret_ty)).collect();
        let tuple_ty = tys.iter().map(|t| format!("({})", t)).collect::<Vec<_>>().join(" \\<times> ");
        let recs: Vec<String> = members.iter().map(|d| format!("rec_{}", d.name)).collect();
        let binder = if k == 1 { recs[0].clone() } else { format!("({})", recs.join(", ")) };
        let lam = |d: &FunDef<'_>| if d.params.is_empty() { String::new() } else { format!("\\<lambda>{}. ", d.params.join(" ")) };
        let bodies: Vec<String> = members
            .iter()
            .map(|d| {
                let body = subst_markers(fe, &d.body, Some(&set), &names);
                format!("{}FunctionBody \\<lbrakk>\n{}  \\<rbrakk>", lam(d), indent(&body, 4))
            })
            .collect();
        let bottoms: Vec<String> = members
            .iter()
            .map(|d| format!("{}FunctionBody \\<lbrakk> panic!(\"out of fuel\") \\<rbrakk>", lam(d)))
            .collect();
        writeln!(
            out,
            "text \\<open>Recursive group {}: defined by iterating {} \\<^term>\\<open>urust_fuel\\<close> times.\\<close>\n",
            members.iter().map(|d| d.name.clone()).collect::<Vec<_>>().join(", "),
            step
        )
        .unwrap();
        let tuple = |xs: &[String]| if xs.len() == 1 { format!("({})", xs[0]) } else { format!("({})", xs.join(",\n   ")) };
        writeln!(
            out,
            "definition \"{}\" :: {} where\n  {}\n",
            step,
            cart(&format!("({}) \\<Rightarrow> ({})", tuple_ty, tuple_ty)),
            cart(&format!("{} \\<equiv> \\<lambda>{}. {}", step, binder, tuple(&bodies)))
        )
        .unwrap();
        let start = tuple(&bottoms);
        for (i, d) in members.iter().enumerate() {
            let iter = format!("(({} ^^ urust_fuel) {})", step, start);
            let proj = if k == 1 {
                iter
            } else {
                let mut s = iter;
                for _ in 0..i {
                    s = format!("(snd {})", s);
                }
                if i + 1 < k { format!("(fst {})", s) } else { s }
            };
            writeln!(out, "(* Rust: {} *)", cmt(&d.rust_path)).unwrap();
            for cm in &d.comments {
                writeln!(out, "(* {} *)", cmt(cm)).unwrap();
            }
            writeln!(
                out,
                "definition \"{}\" :: {} where\n  {}\n",
                d.name,
                cart(&tys[i]),
                cart(&format!("{} \\<equiv> {}", d.name, proj))
            )
            .unwrap();
        }
    }

    fe.fun_defs = defs;
    out
}

fn emit_def(fe: &Frontend<'_>, d: &FunDef<'_>, body: &str) -> String {
    let mut out = String::new();
    writeln!(out, "(* Rust: {} *)", cmt(&d.rust_path)).unwrap();
    for c in &d.comments {
        writeln!(out, "(* {} *)", cmt(c)).unwrap();
    }
    let ty = fe.fun_type(&d.param_tys, &d.ret_ty);
    let lam = if d.params.is_empty() { String::new() } else { format!("\\<lambda>{}. ", d.params.join(" ")) };
    writeln!(
        out,
        "definition \"{}\" :: {} where\n  \\<open>{} \\<equiv> {}FunctionBody \\<lbrakk>\n{}  \\<rbrakk>\\<close>\n",
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
            "(* Rust: {} *)\ndefinition \"{}\" :: {} where\n  {}\n",
            cmt(&f.rust_path),
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
    te.push_str("  imports \"Micro_Rust_Std_Lib.Micro_Rust_Std_Lib\"\nbegin\n\n");
    te.push_str("text \\<open>Types without a uRust model. Replace these declarations by models.\\<close>\n\n");
    for (n, t) in &fe.ext_types {
        let args = if t.arity == 0 {
            String::new()
        } else {
            format!("({}) ", (0..t.arity).map(|i| format!("'t{}", i)).collect::<Vec<_>>().join(", "))
        };
        if t.arity == 0 {
            writeln!(te, "(* {} *)\ntypedecl {}\n", cmt(&t.comment), n).unwrap();
        } else {
            // a one-constructor datatype (a BNF): recursive types may be nested through it. It holds
            // a list of values of each type argument, as an external container may hold none
            // (otherwise a type recursive through it, e.g. a tree of `HashMap`s, would be empty).
            let vs: Vec<String> = (0..t.arity).map(|i| format!("\\<open>'t{} list\\<close>", i)).collect();
            writeln!(te, "(* {} *)\ndatatype {}{} = Opaque_{} {}\n", cmt(&t.comment), args, n, n, vs.join(" ")).unwrap();
        }
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
    for ic in &fe.item_comments {
        writeln!(fu, "(* {} *)", cmt(ic)).unwrap();
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
