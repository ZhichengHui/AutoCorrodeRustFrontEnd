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
use crate::frontend::{ExtFun, FnKey, Frontend, FunDef, Inst, field_ty, one_line, paren_ty};
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
    let adt_sccs = collect_adts(&mut fe);
    let types_text = emit_types(&mut fe, &adt_sccs);

    // ---------------- functions / consts ----------------
    let items = tcx.hir_crate_items(());
    let mut bodies: Vec<DefId> = vec![];
    for id in items.free_items() {
        let item = tcx.hir_item(id);
        let did = item.owner_id.to_def_id();
        match item.kind {
            hir::ItemKind::Fn { .. } if !fe.bodiless_intrinsic(did) => bodies.push(did),
            hir::ItemKind::Const(..) => bodies.push(did),
            hir::ItemKind::Static(m, ..) => {
                if m.is_mut() {
                    fe.item_placeholder("static mut", tcx.def_span(did));
                } else {
                    bodies.push(did);
                }
            }
            hir::ItemKind::TraitAlias(..) => fe.item_placeholder("trait alias", tcx.def_span(did)),
            hir::ItemKind::GlobalAsm { .. } => fe.item_placeholder("global assembly", item.span),
            hir::ItemKind::Impl(_) => {
                // destructors are called where Rust drops the values (see `BodyTr::drop_glue`)
                if !tcx.is_automatically_derived(did)
                    && let Some(tr) = tcx.impl_opt_trait_ref(did)
                    && tcx.is_lang_item(tr.skip_binder().def_id, LangItem::Drop)
                {
                    fe.has_drop_impls = true;
                }
            }
            hir::ItemKind::ForeignMod { items: fitems, .. } => {
                for fi in fitems.iter() {
                    let fdid = fi.owner_id.to_def_id();
                    if matches!(tcx.def_kind(fdid), DefKind::Fn) {
                        fe.ext_fun(fdid, true);
                    } else {
                        fe.item_placeholder("foreign static", tcx.def_span(fdid));
                    }
                }
            }
            _ => {}
        }
    }
    for id in items.impl_items() {
        let ii = tcx.hir_impl_item(id);
        let did = ii.owner_id.to_def_id();
        if tcx.is_automatically_derived(tcx.parent(did)) {
            continue;
        }
        match ii.kind {
            hir::ImplItemKind::Fn(..) | hir::ImplItemKind::Const(..) => bodies.push(did),
            // its uses are normalised to the type it defines
            hir::ImplItemKind::Type(..) => {}
        }
    }
    // default methods are generic over `Self`: translated at the instances they are called at
    let default_methods: Vec<DefId> = items
        .trait_items()
        .filter(|&id| matches!(tcx.hir_trait_item(id).kind, hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(_))))
        .map(|id| id.owner_id.to_def_id())
        .collect();
    fe.mono_fns = mono_fns(&fe, &bodies, &default_methods);
    for &d in &bodies {
        fe.def_name(d);
    }
    // A function with const generic parameters only at its instances (see `local_callee`). A
    // function translated per instance (see `mono_fns`) that the crate does not export is
    // translated generically only when a definition refers to its generic version, or when it
    // has no instance (see below): its generic version cannot translate what needs the instances.
    let exported = tcx.effective_visibilities(());
    let deferred: HashSet<DefId> = bodies
        .iter()
        .copied()
        .filter(|&d| fe.mono_fns.contains(&d) && !fe.has_const_params(d) && d.as_local().is_some_and(|l| !exported.is_exported(l)))
        .collect();
    for &d in &bodies {
        if !fe.has_const_params(d) && !deferred.contains(&d) {
            translate_item(&mut fe, (d, Inst::Generic));
        }
    }
    // each local implementation's copies of the default methods it does not override (its
    // dictionaries' fields)
    for id in items.free_items() {
        let imp = id.owner_id.to_def_id();
        if !matches!(tcx.def_kind(imp), DefKind::Impl { of_trait: true }) || tcx.is_automatically_derived(imp) {
            continue;
        }
        let tr = tcx.impl_trait_ref(imp).instantiate_identity().skip_normalization().def_id;
        let implementors = tcx.impl_item_implementor_ids(imp);
        let fields = fe.dict_methods(tr);
        for &m in &default_methods {
            if tcx.trait_of_assoc(m) == Some(tr) && fields.contains(&m) && !implementors.contains_key(&m) {
                fe.impl_copy(m, imp);
            }
        }
    }
    // instances called from the translated bodies, and from those instances; then the deferred
    // generic versions that are referred to or whose functions have no instance (and what they call);
    // a default method that no local implementation uses (nor these): generically, with the
    // dictionary of `Self` (for the implementations outside the crate)
    loop {
        while let Some(key) = fe.pending.pop() {
            translate_item(&mut fe, key);
        }
        let needed: Vec<DefId> = deferred
            .iter()
            .copied()
            .filter(|&d| {
                let g = (d, Inst::Generic);
                !fe.fun_defs.iter().any(|f| f.key == g)
                    && (fe.fun_defs.iter().any(|f| f.calls.0.contains(&g)) || !fe.fun_defs.iter().any(|f| f.key.0 == d))
            })
            .collect();
        let unused_defaults: Vec<DefId> =
            default_methods.iter().copied().filter(|&d| !fe.fun_defs.iter().any(|f| f.key.0 == d)).collect();
        if needed.is_empty() && unused_defaults.is_empty() {
            break;
        }
        for d in needed.into_iter().chain(unused_defaults) {
            translate_item(&mut fe, (d, Inst::Generic));
        }
    }
    for &d in &bodies {
        if fe.has_const_params(d) && !fe.fun_defs.iter().any(|f| f.key.0 == d) {
            fe.item_placeholder("function with const generic parameters (not called at constant arguments)", tcx.def_span(d));
        }
    }

    let (funs_text, alloc_decls) = emit_funs(&mut fe);
    let types_text = types_text + &fe.dict_decls() + &alloc_decls;
    write_all(&mut fe, opts, types_text, funs_text);
}

/// Collect and classify the local ADTs (see the fields of `Frontend`); returns their groups,
/// used ones first.
fn collect_adts<'tcx>(fe: &mut Frontend<'tcx>) -> Vec<Vec<DefId>> {
    let tcx = fe.tcx;
    let mut adts: Vec<DefId> = vec![];
    for id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(id);
        let did = item.owner_id.to_def_id();
        match item.kind {
            hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => adts.push(did),
            hir::ItemKind::Union(..) => fe.item_placeholder("union (declared as an abstract type)", tcx.def_span(did)),
            _ => {}
        }
    }
    // the field types of the generic ADTs (see `Frontend::field_ty`), on which all of the following
    // is decided
    let fields: HashMap<DefId, Vec<Ty<'tcx>>> = adts
        .iter()
        .map(|&d| {
            let env = ty::TypingEnv::post_analysis(tcx, d);
            let own = ty::GenericArgs::identity_for_item(tcx, d);
            (d, tcx.adt_def(d).all_fields().map(|f| field_ty(tcx, f, own, env)).collect())
        })
        .collect();
    // the types occurring in the fields of `d`: the field types and their parts
    let field_subtypes = |d: DefId| fields[&d].iter().flat_map(|t| t.walk().filter_map(|g| g.as_type()));
    // type dependency graph
    let adt_set: HashSet<DefId> = adts.iter().copied().collect();
    let deps = |did: DefId| -> Vec<DefId> {
        field_subtypes(did)
            .filter_map(|t| match t.kind() {
                ty::Adt(d, _) if adt_set.contains(&d.did()) => Some(d.did()),
                _ => None,
            })
            .collect()
    };
    let adt_sccs = sccs(&adts, &deps);
    let opaque = |fe: &mut Frontend<'tcx>, comp: &[DefId], why: &'static str, what: &str| {
        for &d in comp {
            fe.opaque_adts.insert(d, why);
            fe.item_placeholder(what, tcx.def_span(d));
        }
    };
    // associated types of an ADT's type parameters in its fields (`S::Unit` in
    // `struct H<S: Shape> { u: S::Unit }`) become extra type parameters of its datatype; the
    // groups come after the ADTs they use
    for comp in &adt_sccs {
        for &d in comp {
            // external ADTs in the fields first: their datatypes may take associated types too
            fe.register_ext_adts(&fields[&d]);
            let ps = fe.projections(d, &fields[&d]);
            if !ps.is_empty() {
                fe.adt_projs.insert(d, ps);
            }
        }
    }
    // the datatypes of a HOL `datatype ... and ...` have the same type parameters, and each recurs
    // with exactly these, in order (`emit_types` names them after the first member): a group of
    // ADTs with different numbers of type parameters, or in which an ADT `d` refers to a member
    // with other type arguments than `d`'s own parameters, is a placeholder
    let own_types = |d: DefId| -> Vec<Ty<'_>> { ty::GenericArgs::identity_for_item(tcx, d).types().collect() };
    for comp in &adt_sccs {
        // the members of a group would have to share their extra type parameters (see `adt_projs`)
        if comp.len() > 1 && comp.iter().any(|d| fe.adt_projs.contains_key(d)) {
            opaque(
                fe,
                comp,
                "mutually recursive with associated types",
                "mutually recursive type with an associated type of a type parameter in a field (declared as an abstract type)",
            );
            continue;
        }
        let arity = own_types(comp[0]).len();
        let nonuniform = comp.iter().any(|&d| {
            let own = own_types(d);
            own.len() != arity
                || field_subtypes(d)
                    .any(|t| matches!(t.kind(), ty::Adt(e, args) if comp.contains(&e.did()) && args.types().collect::<Vec<_>>() != own))
        });
        if nonuniform {
            opaque(fe, comp, "non-uniformly recursive", "non-uniformly recursive type (declared as an abstract type)");
        }
    }
    // a shared reference `&T` is a value of `T`, so a type whose every value contains a value of
    // the same type through shared references (e.g. `struct Node(&'static Node)`, whose values are
    // cycles of statics) has no finite values, and its HOL datatype (a least fixpoint) is empty
    let mut known = HashSet::new();
    let finite: HashSet<DefId> = adts
        .iter()
        .copied()
        .filter(|&d| {
            let t = tcx.type_of(d).instantiate_identity().skip_normalization();
            fe.finite_ty(t, ty::TypingEnv::post_analysis(tcx, d), &adt_set, &mut vec![], &mut known)
        })
        .collect();
    for comp in &adt_sccs {
        if !comp.iter().all(|d| finite.contains(d)) {
            opaque(
                fe,
                comp,
                "without finite values",
                "type without finite values (a shared reference is its referent), or in a recursive group with one (declared as an abstract type)",
            );
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
    // ADTs containing `&mut` references, directly or through other local ADTs, or through the
    // standard types whose models hold references (see `Frontend::ty`)
    loop {
        let mut changed = false;
        for &d in &adts {
            if fe.ref_adts.contains(&d) {
                continue;
            }
            let needs = field_subtypes(d).any(|t| match t.kind() {
                ty::Ref(_, _, m) => m.is_mut(),
                ty::Adt(a, _) => fe.ref_adts.contains(&a.did()) || matches!(fe.std_adt(a.did()), Some("SliceIterMut" | "HashMapEntry")),
                _ => false,
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
    for &d in &adts {
        fe.adt_name(d);
    }
    adt_sccs
}

/// The calls of a body that only an instance can translate (`dependent`): of trait methods that are
/// not dictionary fields (see `Frontend::dict_methods`: e.g. with generic parameters of their own)
/// at arguments with the body's generic parameters; and the calls of local functions at such
/// arguments (`callees`). In a crate with destructors, also a binding or an expression whose type
/// has generic parameters: only an instance knows whether dropping it runs a destructor (see
/// `BodyTr::needs_glue`).
struct GenericCalls<'a, 'tcx> {
    fe: &'a Frontend<'tcx>,
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    dependent: bool,
    callees: Vec<DefId>,
}

impl<'a, 'tcx> GenericCalls<'a, 'tcx> {
    fn call(&mut self, did: DefId, args: ty::GenericArgsRef<'tcx>) {
        if !args.has_param() {
            return;
        }
        // a method of `HashMap` or of its `Entry`, `<[T]>::sort`, `Vec::dedup`: their models need
        // the equality or order of the key or element type to be structural or known, which only
        // an instance shows (see `BodyTr::std_call`)
        let parent = self.tcx.parent(did);
        if matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: false }) && self.fe.is_std(did) {
            let name = self.tcx.item_name(did);
            let needs_instance = match self.tcx.type_of(parent).instantiate_identity().skip_normalization().kind() {
                ty::Adt(d, _) => match self.fe.std_adt(d.did()) {
                    Some("HashMap" | "HashMapEntry") => true,
                    Some("Vec") => name.as_str() == "dedup",
                    _ => false,
                },
                ty::Slice(_) => name.as_str() == "sort",
                _ => false,
            };
            if needs_instance {
                self.dependent = true;
                return;
            }
        }
        if let Some(tr) = self.tcx.trait_of_assoc(did) {
            // a call of a value of a type parameter bounded by an `Fn` trait is a call of a function
            // value (see `Frontend::fn_param_types`)
            if !self.fe.is_fn_trait(tr) && !self.fe.dict_methods(tr).contains(&did) {
                self.dependent = true;
            }
        } else if did.is_local() {
            self.callees.push(did);
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for GenericCalls<'a, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_pat(&mut self, p: &'tcx hir::Pat<'tcx>) {
        if self.fe.has_drop_impls && matches!(p.kind, hir::PatKind::Binding(..)) && self.typeck.pat_ty(p).has_param() {
            self.dependent = true;
        }
        intravisit::walk_pat(self, p);
    }

    fn visit_expr(&mut self, e: &'tcx hir::Expr<'tcx>) {
        // a value of a type with parameters (a temporary dropped at once, an argument, ...)
        if self.fe.has_drop_impls && self.typeck.expr_ty(e).has_param() {
            self.dependent = true;
        }
        if let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) {
            self.call(did, self.typeck.node_args(e.hir_id));
        }
        if let hir::ExprKind::Call(callee, _) = e.kind {
            if let ty::FnDef(did, args) = *self.typeck.expr_ty_adjusted(callee).peel_refs().kind() {
                self.call(did, args.skip_binder());
            }
        }
        intravisit::walk_expr(self, e);
    }
}

/// The generic functions translated per instance (besides once generically): the trait default
/// methods that are not dictionary fields (they have no copies for implementations, see `run`),
/// and the generic functions with a call only an instance translates (see `GenericCalls`),
/// directly or through other such functions.
fn mono_fns<'tcx>(fe: &Frontend<'tcx>, bodies: &[DefId], default_methods: &[DefId]) -> HashSet<DefId> {
    let tcx = fe.tcx;
    let mut mono: HashSet<DefId> = default_methods
        .iter()
        .copied()
        .filter(|&m| !fe.dict_methods(tcx.trait_of_assoc(m).expect("a default method is a trait item")).contains(&m))
        .collect();
    let mut callees: Vec<(DefId, Vec<DefId>)> = vec![];
    for &did in bodies {
        if !fe.local_fn_with_body(did) {
            continue;
        }
        let ld = did.expect_local();
        let mut v = GenericCalls { fe, tcx, typeck: tcx.typeck(ld), dependent: false, callees: vec![] };
        v.visit_body(tcx.hir_body_owned_by(ld));
        if v.dependent || fe.has_const_params(did) {
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

/// The type variable of the `k`-th projection of a datatype or generic function (type
/// parameters' variables are `'r..`, see `names::tvar_name`).
fn proj_tvar(k: usize) -> String {
    format!("'proj{}", k)
}

fn alias_of(t: Ty<'_>) -> ty::AliasTy<'_> {
    match t.kind() {
        ty::Alias(_, a) => *a,
        _ => unreachable!("projections are aliases"),
    }
}

/// A generic function is a HOL constant polymorphic also in the associated types of its type
/// parameters in its signature (`T::Output` in `fn first<T: Index<usize>>(x: &T) -> &T::Output`):
/// they are type variables, which each instance fixes (`Output = u32` at `T = Buf`). Independent
/// variables cannot express that two associated types of the same type are equal through an
/// implementation (e.g. `<T as IntoIterator>::Item` and `<T as Iterator>::Item`), so with two of
/// them the signature's types are not modelled. One occurring only in the body is not a variable
/// (it would be an extra type variable of the definition).
fn proj_tvars<'tcx>(fe: &Frontend<'tcx>, did: DefId, sig_tys: &[Ty<'tcx>]) -> Option<HashMap<ty::AliasTy<'tcx>, String>> {
    let ps: Vec<ty::AliasTy<'tcx>> = fe.projections(did, sig_tys).into_iter().map(alias_of).collect();
    let selves: Vec<Ty<'tcx>> = ps.iter().filter(|a| a.try_to_projection().is_some()).map(|a| a.args.type_at(0)).collect();
    if (1..selves.len()).all(|i| !selves[..i].contains(&selves[i])) {
        Some(ps.into_iter().enumerate().map(|(k, a)| (a, proj_tvar(k))).collect())
    } else {
        None
    }
}

/// Translate the function or constant `key` and record its definition.
fn translate_item<'tcx>(fe: &mut Frontend<'tcx>, key: FnKey<'tcx>) {
    let mut fd = translate_fn(fe, key);
    // the projections' type variables (see `proj_tvars`) and the function types of `Fn`-bounded
    // parameters are those of one definition; they are kept for its allocation record (see
    // `alloc_sets`)
    fd.proj_ctx = fe.proj_tvars.take();
    fd.fn_ctx = std::mem::take(&mut fe.fn_params);
    fe.fun_defs.push(fd);
}

fn translate_fn<'tcx>(fe: &mut Frontend<'tcx>, key: FnKey<'tcx>) -> FunDef<'tcx> {
    let tcx = fe.tcx;
    let did = key.0;
    let ld: LocalDefId = did.expect_local();
    let is_fn = matches!(tcx.def_kind(did), DefKind::Fn | DefKind::AssocFn);
    let name = fe.fn_name(key);
    // the dictionary parameters come first (see `crate::dict`)
    let dicts = if is_fn { fe.dict_params(key) } else { vec![] };
    let rust_path = match key.1 {
        Inst::Generic => tcx.def_path_str(did),
        Inst::Mono(args) => tcx.def_path_str_with_args(did, args),
        Inst::ImplCopy(imp) => format!("{} (default method, for {})", tcx.def_path_str(did), tcx.def_path_str(imp)),
    };
    let (params, ret): (Vec<(String, bool)>, (String, bool)) = if is_fn {
        let sig = tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(did).instantiate_identity().skip_normalization());
        // an instance's types at its arguments; a generic item's projections normalised in its own
        // typing environment (e.g. `<Iter<T> as Iterator>::Item` through the impl)
        let at = |t: Ty<'tcx>| fe.at_key(key, t);
        let tys: Vec<Ty<'tcx>> = sig.inputs_and_output.iter().map(at).collect();
        if !matches!(key.1, Inst::Mono(_)) {
            fe.register_ext_adts(&tys);
            // the associated types of the dictionaries' slots are type variables too
            let env = fe.inst_env(key);
            let mut all = tys.clone();
            for (r, _) in &dicts {
                all.extend(fe.dict_slots(*r).into_iter().map(|t| {
                    tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(t)).unwrap_or(t)
                }));
            }
            // and so are those in the types of the `Fn` bounds (see `Frontend::fn_param_types`)
            let owner = match key.1 { Inst::ImplCopy(imp) => imp, _ => did };
            for (_, ins, ret) in fe.fn_bounded_params(owner) {
                all.extend(ins.into_iter().chain([ret]).map(|t| {
                    let t = tcx.erase_and_anonymize_regions(t);
                    tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(t)).unwrap_or(t)
                }));
            }
            fe.proj_tvars = proj_tvars(fe, owner, &all);
            fe.fn_params = fe.fn_param_types(owner);
        }
        let (out, ins) = tys.split_last().expect("a signature has an output");
        let env = fe.inst_env(key);
        let mut ps: Vec<(String, bool)> = dicts.iter().map(|(r, _)| (fe.dict_type(*r, env), true)).collect();
        ps.extend(ins.iter().map(|t| fe.ty_modelled(*t)));
        (ps, fe.ty_modelled(*out))
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
        n_dicts: dicts.len(),
        proj_ctx: None,
        fn_ctx: HashMap::new(),
    };
    let sp = tcx.def_span(did);
    let fn_placeholder = |fe: &mut Frontend<'tcx>, fd: &mut FunDef<'tcx>, msg: &str| {
        let m = fe.placeholder(msg, Some(sp));
        fd.params = (0..fd.param_tys.len()).map(|i| format!("arg_{}", i)).collect();
        fd.body = format!("unimplemented!(\"{}\")", names::string_token(&m));
        fd.calls.clear();
        fd.comments.push(m);
    };
    if is_fn && tcx.asyncness(did).is_async() {
        fn_placeholder(fe, &mut fd, "async fn");
        return fd;
    }
    // the C-variadic parameter `...` is not part of the signature but is bound in the body
    if is_fn && tcx.fn_sig(did).skip_binder().c_variadic() {
        fn_placeholder(fe, &mut fd, "C-variadic function");
        return fd;
    }
    // an instance has values for the const generic parameters (see `BodyTr::path_value`)
    if !matches!(key.1, Inst::Mono(_)) && fe.has_const_params(did) {
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
        let msg = if is_fn {
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
    let mut bt = BodyTr::new(fe, key);
    let res = bt.fn_body(body);
    let calls = std::mem::take(&mut bt.calls);
    let comments = std::mem::take(&mut bt.comments);
    match res {
        Ok((params, text)) => {
            fd.params = dicts.iter().map(|(_, n)| n.clone()).chain(params).collect();
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
        // the type parameters of the first member, shared by the group (see `run`)
        let shared: Vec<Ty<'tcx>> = ty::GenericArgs::identity_for_item(tcx, comp[0]).types().collect();
        let tparams: Vec<String> = shared
            .iter()
            .map(|t| match t.kind() {
                ty::Param(p) => names::tvar_name(p.name.as_str()),
                _ => unreachable!("identity arguments are parameters"),
            })
            .collect();
        for &d in comp {
            let def = tcx.adt_def(d);
            let tn = fe.adt_name(d);
            // `d`'s k-th type parameter is the group's k-th
            let mut k = 0;
            let to_shared = ty::GenericArgs::for_item(tcx, d, |p, _| match p.kind {
                ty::GenericParamDefKind::Type { .. } => {
                    k += 1;
                    shared[k - 1].into()
                }
                _ => tcx.mk_param_from_def(p),
            });
            let (own, env) = (ty::GenericArgs::identity_for_item(tcx, d), ty::TypingEnv::post_analysis(tcx, d));
            let shared_field_ty = |f: &ty::FieldDef| ty::EarlyBinder::bind(tcx, field_ty(tcx, f, own, env)).instantiate(tcx, to_shared).skip_normalization();
            // a group with associated types in fields has one member (see `run`)
            let projs = fe.adt_projs.get(&d).cloned().unwrap_or_default();
            let proj_names: Vec<String> = (0..projs.len()).map(proj_tvar).collect();
            fe.proj_tvars = Some(projs.into_iter().map(alias_of).zip(proj_names.iter().cloned()).collect());
            let has_const = tcx.generics_of(d).own_params.iter().any(|p| matches!(p.kind, ty::GenericParamDefKind::Const { .. }));
            let mut tparams = tparams.clone();
            tparams.extend(proj_names);
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
                let ftys: Vec<String> = v.fields.iter().map(|f| fe.ty(shared_field_ty(f))).collect();
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
                    let ftys: Vec<String> = v.fields.iter().map(|f| fe.ty(shared_field_ty(f))).collect();
                    let args: Vec<String> = ftys.iter().map(|t| cart(t)).collect();
                    ctors.push(if args.is_empty() { cn.clone() } else { format!("{} {}", cn, args.join(" ")) });
                    if !ftys.is_empty() {
                        after.push_str(&ctor_fun(&format!("{}_mk", cn), &cn, &ftys, &head));
                    }
                }
                decls.push(format!("{} =\n    {}", head, ctors.join("\n  | ")));
            }
        }
        fe.proj_tvars = None;
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
        "definition \"{}\" :: {} where\n  [crush_inline]: {}\n\n",
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

/// The markers (`\u{1}<kind><n>\u{2}`) in `text`, with those in the dictionaries and arguments of
/// the generic calls among them (see `GenCall`), transitively.
fn markers_in(fe: &Frontend<'_>, text: &str, out: &mut Vec<(char, usize)>) {
    let mut rest = text;
    while let Some(i) = rest.find('\u{1}') {
        let j = rest[i..].find('\u{2}').expect("a marker is closed") + i;
        let kind = rest[i + 1..].chars().next().expect("a marker has a kind");
        let n: usize = rest[i + 2..j].parse().expect("a marker has an index");
        out.push((kind, n));
        if matches!(kind, 'F' | 'V') {
            let c = &fe.gen_calls[n];
            for t in c.dicts.iter().chain(c.args.iter().flatten()) {
                markers_in(fe, t, out);
            }
        }
        rest = &rest[j + 1..];
    }
}

/// Allocation records beyond this size are not built (polymorphic recursion would make them grow
/// without bound).
const MAX_ALLOCS: usize = 64;

/// The allocation records (see `BodyTr::alloc`): for each translation, the types with generic
/// parameters of the cells allocated by its body and by the generic functions it calls (at its
/// generic parameters), with their HOL types, in order; and the translations whose record would
/// exceed `MAX_ALLOCS`.
struct Allocs<'tcx> {
    sets: HashMap<FnKey<'tcx>, Vec<(Ty<'tcx>, String)>>,
    overflow: HashSet<FnKey<'tcx>>,
    /// the datatypes' names
    names: HashMap<FnKey<'tcx>, String>,
}

impl<'tcx> Allocs<'tcx> {
    fn set(&self, k: FnKey<'tcx>) -> &[(Ty<'tcx>, String)] {
        self.sets.get(&k).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

/// `t`, a type of the body of a callee, at the generic arguments `kargs` of a call in the body of
/// `caller`, normalised there.
fn at_call<'tcx>(fe: &Frontend<'tcx>, caller: FnKey<'tcx>, kargs: ty::GenericArgsRef<'tcx>, t: Ty<'tcx>) -> Ty<'tcx> {
    let tcx = fe.tcx;
    let x = ty::EarlyBinder::bind(tcx, t).instantiate(tcx, kargs);
    tcx.erase_and_anonymize_regions(tcx.try_normalize_erasing_regions(fe.inst_env(caller), x).unwrap_or_else(|_| x.skip_normalization()))
}

/// The HOL type of `t` in the context of the definition `d` (its projections' type variables and
/// `Fn`-bounded parameters).
fn hol_in<'tcx>(fe: &mut Frontend<'tcx>, d: &FunDef<'tcx>, t: Ty<'tcx>) -> String {
    let saved = (fe.proj_tvars.take(), std::mem::take(&mut fe.fn_params));
    fe.proj_tvars = d.proj_ctx.clone();
    fe.fn_params = d.fn_ctx.clone();
    let h = fe.ty(t);
    (fe.proj_tvars, fe.fn_params) = saved;
    h
}

fn alloc_sets<'tcx>(fe: &mut Frontend<'tcx>, defs: &[FunDef<'tcx>]) -> Allocs<'tcx> {
    let mut sets: HashMap<FnKey<'tcx>, Vec<(Ty<'tcx>, String)>> = HashMap::new();
    let mut calls: Vec<Vec<usize>> = vec![];
    for d in defs {
        let mut ms = vec![];
        markers_in(fe, &d.body, &mut ms);
        let set = sets.entry(d.key).or_default();
        for &(k, n) in &ms {
            if k == 'A' {
                let (_, t, ref h) = fe.alloc_sites[n];
                if !set.iter().any(|(u, _)| *u == t) {
                    set.push((t, h.clone()));
                }
            }
        }
        calls.push(ms.iter().filter(|(k, _)| matches!(k, 'F' | 'V')).map(|&(_, n)| n).collect());
    }
    let mut overflow = HashSet::new();
    loop {
        let mut changed = false;
        for (d, cs) in defs.iter().zip(&calls) {
            for &c in cs {
                let (callee, kargs) = (fe.gen_calls[c].callee, fe.gen_calls[c].kargs);
                let needed: Vec<Ty<'tcx>> = sets.get(&callee).into_iter().flatten().map(|(t, _)| *t).collect();
                for t in needed {
                    let ti = at_call(fe, d.key, kargs, t);
                    if !ti.has_param() || sets[&d.key].iter().any(|(u, _)| *u == ti) {
                        continue;
                    }
                    if sets[&d.key].len() >= MAX_ALLOCS {
                        overflow.insert(d.key);
                        continue;
                    }
                    let h = hol_in(fe, d, ti);
                    sets.get_mut(&d.key).expect("every definition has a set").push((ti, h));
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut names = HashMap::new();
    for d in defs {
        if !sets[&d.key].is_empty() && !overflow.contains(&d.key) {
            names.insert(d.key, fe.unique_global(format!("{}_alloc", d.name)));
        }
    }
    Allocs { sets, overflow, names }
}

/// The type variables in the HOL types `tys`, in order, except those every record takes first.
fn tvars_of(tys: &[String], base: &[&str]) -> Vec<String> {
    let mut out: Vec<String> = vec![];
    for t in tys {
        let b = t.as_bytes();
        let mut i = 0;
        while i < b.len() {
            if b[i] == b'\'' {
                let mut j = i + 1;
                while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                    j += 1;
                }
                let v = &t[i..j];
                if j > i + 1 && !base.contains(&v) && !out.iter().any(|o| o == v) {
                    out.push(v.to_string());
                }
                i = j;
            } else {
                i += 1;
            }
        }
    }
    out
}

const ALLOC_BASE: [&str; 6] = ["'s", "'abort", "'i", "'o", "'addr", "'gv"];

/// The allocation record datatype of a definition: one allocator per type of its set.
fn alloc_decl(fe: &Frontend<'_>, name: &str, set: &[(Ty<'_>, String)]) -> (String, String) {
    let fields: Vec<String> = set
        .iter()
        .map(|(_, h)| fe.fun_type(&[h.clone()], &format!("('addr, 'gv, {}) Global_Store.ref", h)))
        .collect();
    let mut tparams: Vec<String> = ALLOC_BASE.iter().map(|s| s.to_string()).collect();
    tparams.extend(tvars_of(&fields, &ALLOC_BASE));
    let decl = format!(
        "datatype ({}) {} =\n  {} {}\n\n",
        tparams.join(", "),
        name,
        name,
        fields.iter().enumerate().map(|(k, f)| format!("({}_{}: {})", name, k, cart(f))).collect::<Vec<_>>().join("\n    ")
    );
    (format!("({}) {}", tparams.join(", "), name), decl)
}

/// The name of the allocation record parameter.
const ALLOC_PARAM: &str = "alloc_record";

/// The allocation record a generic call passes to its callee, if the callee takes one: each
/// allocator is the caller's own (for a type with generic parameters) or the locale's.
fn record_arg<'tcx>(fe: &mut Frontend<'tcx>, allocs: &Allocs<'tcx>, me: FnKey<'tcx>, c: usize) -> Option<String> {
    let (callee, kargs) = (fe.gen_calls[c].callee, fe.gen_calls[c].kargs);
    let name = allocs.names.get(&callee)?.clone();
    let mut fields = vec![];
    for (t, _) in allocs.set(callee).to_vec() {
        let ti = at_call(fe, me, kargs, t);
        fields.push(if ti.has_param() {
            let j = allocs.set(me).iter().position(|(u, _)| *u == ti).expect("the caller's record has its callees' allocators");
            format!("({}_{} {})", allocs.names[&me], j, ALLOC_PARAM)
        } else {
            let h = fe.ty(ti);
            format!("ref_{}.new", fe.need_alloc(&h) + 1)
        });
    }
    Some(format!("({} {})", name, fields.join(" ")))
}

fn subst_markers<'tcx>(
    fe: &mut Frontend<'tcx>,
    allocs: &Allocs<'tcx>,
    me: FnKey<'tcx>,
    body: &str,
    caller_scc: Option<&HashSet<FnKey<'tcx>>>,
    names: &HashMap<FnKey<'tcx>, String>,
) -> String {
    let mut out = String::new();
    let mut rest = body;
    while let Some(i) = rest.find('\u{1}') {
        out.push_str(&rest[..i]);
        let j = rest[i..].find('\u{2}').unwrap() + i;
        let tag = &rest[i + 1..j];
        let kind = &tag[..1];
        let idx: usize = tag[1..].parse().unwrap();
        let s = match kind {
            "A" => {
                let t = fe.alloc_sites[idx].1;
                let j = allocs.set(me).iter().position(|(u, _)| *u == t).expect("a cell's type is in its body's record");
                format!("({}_{} {})", allocs.names[&me], j, ALLOC_PARAM)
            }
            "F" | "V" => {
                let callee = fe.gen_calls[idx].callee;
                // every marked callee is a local item with a body, hence translated
                let name = names.get(&callee).cloned().expect("callee of a call marker is translated");
                let rec = caller_scc.map(|s| s.contains(&callee)).unwrap_or(false);
                let head = if rec { format!("rec_{}", name) } else { name.clone() };
                let mut extra: Vec<String> = fe.gen_calls[idx].dicts.clone().iter().map(|d| subst_markers(fe, allocs, me, d, caller_scc, names)).collect();
                extra.extend(record_arg(fe, allocs, me, idx));
                let f = if extra.is_empty() { head.clone() } else { format!("{} {}", head, extra.join(" ")) };
                match fe.gen_calls[idx].args.clone() {
                    // a value applied to dictionaries or a record is an application: parenthesised, as
                    // the marker it replaces is an argument without parentheses (see `paren_term`)
                    None if extra.is_empty() => f,
                    None => format!("({})", f),
                    Some(args) => {
                        let a: Vec<String> = args.iter().map(|x| subst_markers(fe, allocs, me, x, caller_scc, names)).collect();
                        if !extra.is_empty() {
                            crate::body::term_call(&f, &a)
                        } else if a.is_empty() {
                            if rec { format!("\\<epsilon>\\<open>funcall0 rec_{}\\<close>", name) } else { format!("{}()", name) }
                        } else if a.len() <= 8 {
                            let c = if rec { format!("\\<epsilon>\\<open>rec_{}\\<close>", name) } else { name };
                            format!("{}({})", c, a.join(", "))
                        } else {
                            let wrapped: Vec<String> = a.iter().map(|x| format!("\\<lbrakk>{}\\<rbrakk>", x)).collect();
                            format!("\\<epsilon>\\<open>funcall{} {} {}\\<close>", a.len(), head, wrapped.join(" "))
                        }
                    }
                }
            }
            _ => {
                let key = fe.marker_ids[idx];
                // every marked callee is a local item with a body, hence translated
                let name = names.get(&key).cloned().expect("callee of a call marker is translated");
                let rec = caller_scc.map(|s| s.contains(&key)).unwrap_or(false);
                match (kind, rec) {
                    ("C", false) | ("H", false) => name.clone(),
                    ("Z", false) => format!("{}()", name),
                    ("C", true) => format!("\\<epsilon>\\<open>rec_{}\\<close>", name),
                    ("H", true) => format!("rec_{}", name),
                    ("Z", true) => format!("\\<epsilon>\\<open>funcall0 rec_{}\\<close>", name),
                    _ => unreachable!(),
                }
            }
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

/// The definitions (and the allocation records' datatypes, for the types theory).
fn emit_funs<'tcx>(fe: &mut Frontend<'tcx>) -> (String, String) {
    let mut defs = std::mem::take(&mut fe.fun_defs);
    let allocs = alloc_sets(fe, &defs);
    let mut decls = String::new();
    for d in defs.iter_mut() {
        if allocs.overflow.contains(&d.key) {
            let m = fe.placeholder("mutable locals of generic types in polymorphic recursion (allocation record without bound)", Some(fe.tcx.def_span(d.key.0)));
            d.params = (0..d.param_tys.len()).map(|i| format!("arg_{}", i)).collect();
            d.body = format!("unimplemented!(\"{}\")", names::string_token(&m));
            d.calls.clear();
            d.comments.push(m);
            continue;
        }
        if let Some(n) = allocs.names.get(&d.key) {
            let (t, decl) = alloc_decl(fe, n, allocs.set(d.key));
            writeln!(decls, "(* Rust: allocators of the mutable locals of {} and the functions it calls *)", cmt(&d.rust_path)).unwrap();
            decls.push_str(&decl);
            d.param_tys.insert(d.n_dicts, t);
            d.params.insert(d.n_dicts, ALLOC_PARAM.to_string());
        }
    }
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
            let body = subst_markers(fe, &allocs, d.key, &d.body, None, &names);
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
                let body = subst_markers(fe, &allocs, d.key, &d.body, Some(&set), &names);
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
        let tuple = |xs: &[String]| format!("({})", xs.join(",\n   "));
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
    (out, decls)
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

/// Generated definitions may have type variables in their bodies only (e.g. the element type of an
/// empty list that is only measured): `StdLib_Frontend_Models` instantiates them with `unit`.
const GROUND: &str = "declare [[urust_ground_body_types]]\n\n";

fn write_all(fe: &mut Frontend<'_>, opts: &Options, types_text: String, funs_text: String) {
    let c = &opts.name;
    let dir = Path::new(&opts.out_dir);
    std::fs::create_dir_all(dir).unwrap();
    let ctx = format!("{}_ctx", c);
    let header = |t: &str| format!("(* Generated by urust-frontend from crate `{}`. *)\n\ntheory {}\n", c, t);

    // external / placeholder types
    let mut te = header(&format!("{}_TypesExternal_Template", c));
    te.push_str("  imports \"Micro_Rust_Std_Lib.Micro_Rust_Std_Lib\"\nbegin\n\n");
    te.push_str(GROUND);
    te.push_str("text \\<open>Types without a uRust model. Replace these declarations by models.\\<close>\n\n");
    for (n, t) in &fe.ext_types {
        if !t.ctors.is_empty() {
            continue;
        } else if t.arity == 0 {
            writeln!(te, "(* {} *)\ntypedecl {}\n", cmt(&t.comment), n).unwrap();
        } else {
            // a one-constructor datatype (a BNF): recursive types may be nested through it. It holds
            // a list of values of each type argument, as an external container may hold none
            // (otherwise a type recursive through it, e.g. a tree of `HashMap`s, would be empty).
            let args = (0..t.arity).map(|i| format!("'t{}", i)).collect::<Vec<_>>().join(", ");
            let vs: Vec<String> = (0..t.arity).map(|i| format!("\\<open>'t{} list\\<close>", i)).collect();
            writeln!(te, "(* {} *)\ndatatype ({}) {} = Opaque_{} {}\n", cmt(&t.comment), args, n, n, vs.join(" ")).unwrap();
        }
    }
    te.push_str("end\n");
    // the external ADTs declared with their constructors (see `ExtType::ctors`), each after the
    // ones its fields use; types using each other are one datatype declaration. They are complete
    // translations, not templates: their own theory.
    let mut tx = header(&format!("{}_TypesExternal", c));
    writeln!(tx, "  imports {}_TypesExternal_Template\nbegin\n", c).unwrap();
    tx.push_str(GROUND);
    tx.push_str("text \\<open>External types declared with their constructors (all their fields have models).\\<close>\n\n");
    let mut left: Vec<&String> = fe.ext_types.iter().filter(|(_, t)| !t.ctors.is_empty()).map(|(n, _)| n).collect();
    let mut mks = String::new();
    while !left.is_empty() {
        let ready: Vec<&String> =
            left.iter().copied().filter(|n| fe.ext_types[*n].deps.iter().all(|d| !left.contains(&d))).collect();
        let group = if ready.is_empty() { left.clone() } else { vec![ready[0]] };
        let mut decls = vec![];
        for n in &group {
            let t = &fe.ext_types[*n];
            let head = if t.params.is_empty() { (*n).clone() } else { format!("({}) {}", t.params.join(", "), n) };
            let ctors: Vec<String> = t
                .ctors
                .iter()
                .map(|(c, fs)| if fs.is_empty() { c.clone() } else { format!("{} {}", c, fs.iter().map(|f| cart(f)).collect::<Vec<_>>().join(" ")) })
                .collect();
            writeln!(tx, "(* {} *)", cmt(&t.comment)).unwrap();
            decls.push(format!("{} =\n    {}", head, ctors.join("\n  | ")));
            for (c, fs) in &t.ctors {
                if !fs.is_empty() {
                    mks.push_str(&ctor_fun(&format!("{}_mk", c), c, fs, &head));
                }
            }
        }
        writeln!(tx, "datatype {}\n", decls.join("\nand ")).unwrap();
        left.retain(|n| !group.contains(n));
    }
    tx.push_str(&mks);
    tx.push_str("end\n");

    let mut ty = header(&format!("{}_Types", c));
    writeln!(ty, "  imports {}_TypesExternal\nbegin\n", c).unwrap();
    ty.push_str(GROUND);
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
        "  imports {}_Locale\nbegin\n\n{GROUND}text \\<open>Functions without a definition in this crate. Replace the bodies by uRust models.\\<close>\n\ncontext {}\nbegin\n",
        c, ctx
    )
    .unwrap();
    fx.push_str(&emit_ext_funs(&fe.ext_funs, "external function"));
    fx.push_str("end\n\nend\n");

    let mut ff = header(&format!("{}_FunsForeign_Template", c));
    writeln!(
        ff,
        "  imports {}_Locale\nbegin\n\n{GROUND}text \\<open>Functions declared in \\<^verbatim>\\<open>extern\\<close> blocks. They cannot be replaced by uRust models; their contracts must also state memory effects.\\<close>\n\ncontext {}\nbegin\n",
        c, ctx
    )
    .unwrap();
    ff.push_str(&emit_ext_funs(&fe.foreign_funs, "foreign function"));
    ff.push_str("end\n\nend\n");

    let mut fu = header(&format!("{}_Funs", c));
    writeln!(fu, "  imports {}_FunsExternal_Template {}_FunsForeign_Template\nbegin\n\n{GROUND}context {}\nbegin\n", c, c, ctx).unwrap();
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
        (format!("{}_TypesExternal.thy", c), tx),
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
