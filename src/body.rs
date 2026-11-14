//! Translation of HIR bodies (expressions, statements, patterns) to uRust text.
//!
//! Memory model:
//! * a `let mut` local (or a `mut` parameter / pattern binding) becomes a uRust
//!   mutable local, i.e. a reference allocated with `let mut`; reading it is `*x`;
//! * a value of type `&mut T` is a reference `('addr,'gv,T) Global_Store.ref`;
//! * a value of type `&T` is represented by the value of type `T` (shared
//!   borrows of data without interior mutability are observationally values).

use std::collections::{HashMap, HashSet};

use rustc_ast::ast::{Label, LitKind};
use rustc_hir as hir;
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::{CtorKind, CtorOf, DefKind, Res};
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{BinOpKind, ExprKind, HirId, LoopSource, MatchSource, PatKind, StmtKind, UnOp};
use rustc_middle::traits;
use rustc_middle::ty::adjustment::{Adjust, AutoBorrow, AutoBorrowMutability, DerefAdjustKind, PointerCoercion};
use rustc_middle::ty::{self, GenericArgsRef, ScalarInt, Ty, TyCtxt, TypeFoldable, TypeVisitableExt, TypeckResults};
use rustc_span::{Span, Symbol, sym};

use crate::frontend::{FnKey, Frontend, GenCall, Inst};
use crate::names;

pub struct Unsup(pub String);
type R<T> = Result<T, Unsup>;

fn unsup<T>(msg: impl Into<String>) -> R<T> {
    Err(Unsup(msg.into()))
}

/// `f(args)` for the HOL term `f` of a function value and the uRust arguments `a`.
pub fn term_call(f: &str, a: &[String]) -> String {
    if a.len() <= 8 {
        format!("\\<epsilon>\\<open>{}\\<close>({})", f, a.join(", "))
    } else {
        let wrapped: Vec<String> = a.iter().map(|x| format!("\\<lbrakk>{}\\<rbrakk>", x)).collect();
        format!("\\<epsilon>\\<open>funcall{} ({}) {}\\<close>", a.len(), f, wrapped.join(" "))
    }
}

/// `λns. t`, or `t` without names.
fn lambda(ns: &[String], t: String) -> String {
    if ns.is_empty() { t } else { format!("\\<lambda>{}. {}", ns.join(" "), t) }
}

/// A HOL term as an argument of an application: parenthesised unless it is a name.
fn paren_term(t: &str) -> String {
    if t.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '\u{1}' || c == '\u{2}') { t.to_string() } else { format!("({})", t) }
}

/// The label of a loop as it precedes the uRust loop (`'l: `), or nothing.
fn loop_label(label: Option<Label>) -> String {
    label.map(|l| format!("{}: ", l.ident)).unwrap_or_default()
}

/// `break` or `continue` (`kw`) to `dest`: uRust resolves a label, and the innermost loop without
/// one, as Rust does.
fn loop_jump(kw: &str, dest: hir::Destination) -> Tr {
    Tr::atom(match dest.label {
        Some(l) => format!("{} {};", kw, l.ident),
        None => format!("{};", kw),
    })
}

/// A translated expression with its uRust precedence (1000 = atomic).
#[derive(Clone, Debug)]
struct Tr {
    s: String,
    prec: u32,
}

impl Tr {
    fn atom(s: impl Into<String>) -> Tr { Tr { s: s.into(), prec: 1000 } }
    /// A block `{ ... }`: needs no parentheses as an argument or a `let` value, but does as the
    /// operand of an operator, an index or a field access (its braces make the parse ambiguous).
    fn block(s: impl Into<String>) -> Tr { Tr { s: s.into(), prec: 90 } }
    fn new(s: impl Into<String>, prec: u32) -> Tr { Tr { s: s.into(), prec } }
    /// Render with at least precedence `p`, adding parentheses otherwise.
    fn at(&self, p: u32) -> String {
        // `(|` is the ASCII form of the record bracket: separate it from a closure
        if self.prec >= p { self.s.clone() } else if self.s.starts_with('|') { format!("( {})", self.s) } else { format!("({})", self.s) }
    }
}

/// Place or value.
#[derive(Clone, Debug)]
enum PV {
    Val(Tr),
    /// An expression that evaluates to a reference to the place.
    Ref(Tr),
}

#[derive(Clone)]
struct Local {
    name: String,
    cell: bool,
}

/// The mutability of a binding that is translated by value: a by-value binding, or an immutable
/// `ref` binding (a shared reference is represented by the value it points to). `None` for
/// `ref mut`.
fn by_value(bm: hir::BindingMode) -> Option<hir::Mutability> {
    match bm {
        hir::BindingMode(hir::ByRef::No, m) => Some(m),
        hir::BindingMode(hir::ByRef::Yes(_, hir::Mutability::Not), _) => Some(hir::Mutability::Not),
        hir::BindingMode(hir::ByRef::Yes(..), _) => None,
    }
}

/// The standard range types.
#[derive(Clone, Copy)]
enum RangeKind {
    Range,
    Inclusive,
    From,
    To,
    ToInclusive,
    Full,
}

/// Whether `pat` contains a tuple pattern with a component other than a variable or `_`: uRust's
/// `if let` and `while let` accept only tuples of variables.
/// Whether `t` contains an `impl Trait` type.
fn has_opaque(t: Ty<'_>) -> bool {
    t.walk().any(|g| match g.kind() {
        ty::GenericArgKind::Type(x) => matches!(x.kind(), ty::Alias(_, a) if matches!(a.kind, ty::AliasTyKind::Opaque { .. })),
        _ => false,
    })
}

fn tuple_of_non_variables(pat: &hir::Pat<'_>) -> bool {
    let mut found = false;
    pat.walk(|p| {
        if let PatKind::Tuple(ps, _) = p.kind
            && ps.iter().any(|q| !matches!(q.kind, PatKind::Binding(_, _, _, None) | PatKind::Wild))
        {
            found = true;
        }
        true
    });
    found
}

/// Information about a pattern translation for a uRust `match`/`if let`.
struct PatTr {
    pat: String,
    /// Extra guard conditions (from literal / range sub-patterns).
    conds: Vec<String>,
    /// Statements to run at the start of the arm (mutable bindings).
    prologue: Vec<String>,
    /// Those of them that bind by mutable reference (also needed by a guard).
    refs: Vec<String>,
}

pub struct BodyTr<'a, 'tcx> {
    pub fe: &'a mut Frontend<'tcx>,
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    /// What is translated: the generic body itself, an instance, or a default method's copy.
    key: FnKey<'tcx>,
    locals: HashMap<HirId, Local>,
    /// the mutable reference matched by the `match`/`if let`/`while let` being translated, if
    /// any (see `scrut_place`): patterns bind by mutable reference into it
    match_place: Option<Tr>,
    /// the bindings by mutable reference of the pattern being translated (see `PatTr::refs`)
    pat_refs: Vec<String>,
    fresh: usize,
    pub calls: crate::frontend::DefSet<'tcx>,
    pub comments: Vec<String>,
    /// the dictionary parameters of the body (see `Frontend::dict_params`)
    dicts: Vec<(ty::TraitRef<'tcx>, String)>,
    /// the indexing expressions in places borrowed mutably or assigned (see `mark_mut_place`)
    mut_places: HashSet<HirId>,
    /// the scopes being translated, innermost last (see `DropScope`)
    drop_scopes: Vec<DropScope<'tcx>>,
    /// the uses moving the value of a local with a destructor out, with the local's flag (see `own`)
    moved_uses: HashMap<HirId, String>,
    /// the flags of the locals with a destructor that have one (see `own`)
    local_flags: HashMap<HirId, String>,
    /// the jumps (`break`, `continue`) translated as statements ending a block (see `diverging`):
    /// those after drops, or setting a loop's value
    stmt_jumps: HashMap<HirId, String>,
    /// whether dropping a value of a type runs a destructor (see `needs_glue`)
    glue_cache: std::cell::RefCell<HashMap<Ty<'tcx>, bool>>,
    /// the paths to each local in the body, and the locals a closure captures by value (see `own`)
    local_uses: Option<(HashMap<HirId, Vec<&'tcx hir::Expr<'tcx>>>, HashSet<HirId>)>,
    /// the types whose drop glue is being generated (see `drop_glue`)
    glue_stack: Vec<Ty<'tcx>>,
    /// the mutable locals holding the values of the `loop`s being translated that produce one
    loop_results: HashMap<HirId, String>,
    /// while a dictionary field of an implementation is built (see `impl_dict`): the dictionaries
    /// for the method's own bounds that the field takes, as `λ`-bound names
    own_dicts: Vec<(ty::TraitRef<'tcx>, String)>,
}

/// A local owning a value with a destructor (see `BodyTr::needs_glue`), dropped where its scope
/// ends.
#[derive(Clone)]
struct DropLocal<'tcx> {
    /// the uRust local (a cell if `cell`)
    name: String,
    cell: bool,
    ty: Ty<'tcx>,
    /// the mutable local telling whether the local holds a value (it may be moved out, or not
    /// initialised yet)
    flag: Option<String>,
}

/// A scope being translated: a block, or a function's or closure's body (its parameters), with
/// the locals dropped when it ends; or a loop, the target of `break` and `continue`.
enum DropScope<'tcx> {
    Block(Vec<DropLocal<'tcx>>),
    Body(Vec<DropLocal<'tcx>>),
    Loop(HirId),
}

/// How a use of a local with a destructor treats its value (see `BodyTr::use_kind`).
#[derive(PartialEq)]
enum UseKind {
    /// a place: borrowed, projected, read in part
    Place,
    /// moved out whole
    Move,
}

const FUEL: &str = "#[fuel(\\<epsilon>\\<open>urust_fuel\\<close>)]";

impl<'a, 'tcx> BodyTr<'a, 'tcx> {
    pub fn new(fe: &'a mut Frontend<'tcx>, key: FnKey<'tcx>) -> Self {
        let tcx = fe.tcx;
        let typeck = tcx.typeck(key.0.expect_local());
        let fe_dicts = fe.dict_params(key);
        BodyTr {
            fe,
            tcx,
            typeck,
            key,
            locals: HashMap::new(),
            match_place: None,
            pat_refs: vec![],
            fresh: 0,
            calls: crate::frontend::DefSet::default(),
            comments: vec![],
            dicts: fe_dicts,
            mut_places: HashSet::new(),
            drop_scopes: vec![],
            moved_uses: HashMap::new(),
            local_flags: HashMap::new(),
            stmt_jumps: HashMap::new(),
            glue_cache: Default::default(),
            local_uses: None,
            glue_stack: vec![],
            loop_results: HashMap::new(),
            own_dicts: vec![],
        }
    }

    /// A type or generic arguments from the type-checking results, at the instance's or copy's
    /// arguments.
    fn mono<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(&self, x: T) -> T {
        match self.key.1 {
            Inst::Generic => x,
            _ => self.fe.at_key(self.key, x),
        }
    }

    /// The typing environment of the body: no generic parameters are left in an instance; a copy
    /// has those of its implementation.
    fn typing_env(&self) -> ty::TypingEnv<'tcx> {
        self.fe.inst_env(self.key)
    }

    fn node_ty(&self, hid: HirId) -> Ty<'tcx> { self.mono(self.typeck.node_type(hid)) }
    fn pat_ty(&self, p: &hir::Pat<'tcx>) -> Ty<'tcx> { self.mono(self.typeck.pat_ty(p)) }
    fn node_args(&self, hid: HirId) -> GenericArgsRef<'tcx> { self.mono(self.typeck.node_args(hid)) }

    fn fresh(&mut self, base: &str) -> String {
        self.fresh += 1;
        format!("{}_{}", base, self.fresh)
    }

    /// The placeholder term for an expression of type `t`, marked by `marker`. It has the HOL
    /// type of the Rust expression it replaces, so that the overloaded operators applied to it
    /// remain resolvable.
    fn placeholder_term(&mut self, marker: &str, t: Ty<'tcx>) -> Tr {
        let msg = names::string_token(marker);
        if t.is_never() {
            return Tr::new(format!("unimplemented!(\"{}\")", msg), 999);
        }
        let h = self.hty(t);
        Tr::atom(format!(
            "\\<epsilon>\\<open>(unimplemented (STR ''{}'') :: (_, {}, _, _, _, _) expression)\\<close>",
            msg, h
        ))
    }

    /// The HOL type of the body's type `t`. (A type variable left only in the body, e.g. of a
    /// type parameter given only by turbofish, is instantiated with `unit` by AutoCorrode's
    /// `urust_ground_body_types`, see `translate::GROUND`.)
    fn hty(&mut self, t: Ty<'tcx>) -> String {
        // normalised as the signature is (`translate`): in a generic body, in the item's own typing
        // environment, which also reveals its `impl Trait` types; an instance's types are already
        let t = match self.key.1 {
            Inst::Generic => crate::frontend::normalize(self.tcx, self.typing_env(), ty::Unnormalized::new_wip(t)),
            _ => t,
        };
        self.fe.ty(t)
    }

    /// `{ let tmp = v; ⟪tmp :: h⟫ }`: the value `v` stated to have the HOL type `h`.
    fn typed(&mut self, base: &str, v: Tr, h: &str) -> Tr {
        let tmp = self.fresh(base);
        Tr::block(format!("{{ let {} = {}; \\<llangle>{} :: {}\\<rrangle> }}", tmp, v.at(20), tmp, h))
    }

    fn ty_of(&self, e: &hir::Expr<'tcx>) -> Ty<'tcx> { self.mono(self.typeck.expr_ty(e)) }
    fn ty_adj(&self, e: &hir::Expr<'tcx>) -> Ty<'tcx> { self.mono(self.typeck.expr_ty_adjusted(e)) }

    /// `str` or `String` (the list of the UTF-8 bytes, see `Frontend::ty`).
    fn str_like(&self, t: Ty<'tcx>) -> bool {
        t.is_str() || matches!(t.kind(), ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("String"))
    }

    /// A slice, array or `Vec` (possibly behind references): a uRust list.
    fn list_like(&self, t: Ty<'tcx>) -> bool {
        match t.peel_refs().kind() {
            ty::Slice(_) | ty::Array(..) => true,
            ty::Adt(def, _) => self.fe.std_adt(def.did()) == Some("Vec"),
            _ => false,
        }
    }

    fn is_vec(&self, t: Ty<'tcx>) -> bool {
        matches!(t.kind(), ty::Adt(def, _) if self.fe.std_adt(def.did()) == Some("Vec"))
    }

    /// The elements of a `Vec` (AutoCorrode's `rvec`, see `Frontend::ty`) as a list: the
    /// `rvec_elems` of a value, the reference focused on them of a reference.
    fn vec_elems(&self, pv: PV) -> PV {
        match pv {
            PV::Val(v) => PV::Val(Tr::new(format!("\\<llangle>rvec_elems\\<rrangle>\\<^sub>1({})", v.s), 999)),
            PV::Ref(r) => PV::Ref(self.vec_elems_ref(&r)),
        }
    }

    /// The reference to the elements of the `Vec` that the reference `r` refers to.
    fn vec_elems_ref(&self, r: &Tr) -> Tr {
        Tr::new(format!("\\<llangle>focus_reference rvec_elems_focus\\<rrangle>\\<^sub>1({})", r.s), 999)
    }

    /// The layout (size and alignment, AutoCorrode's `elem_layout`) of the element type `t` of a
    /// `Vec`: rustc's; for a type with parameters, AutoCorrode's unspecified `rvec_layout_of`.
    fn elem_layout(&mut self, t: Ty<'tcx>) -> Tr {
        if t.has_param() {
            return Tr::atom(format!("\\<llangle>rvec_layout_of TYPE({})\\<rrangle>", self.hty(t)));
        }
        let env = ty::TypingEnv::fully_monomorphized();
        let l = self.tcx.layout_of(env.as_query_input(t)).expect("the element type of a `Vec` has a layout");
        Tr::atom(format!("\\<llangle>make_elem_layout {} {}\\<rrangle>", l.size.bytes(), l.align.abi.bytes()))
    }

    /// The layout of the elements of the `Vec` type `t`.
    fn vec_layout(&mut self, t: Ty<'tcx>) -> Tr {
        let ty::Adt(_, args) = t.peel_refs().kind() else { panic!("not a `Vec`: {}", t) };
        self.elem_layout(args.type_at(0))
    }

    /// Bind the pattern variable `hid` to the uRust local `name`; a `mut` binding is a mutable
    /// local (a cell), which needs storage for its type: returns its allocator, if not the
    /// locale's (see `alloc`).
    fn declare(&mut self, hid: HirId, name: &str, m: hir::Mutability) -> R<Option<String>> {
        // a binding with a destructor is supported where it owns its value (see `declare_owned`)
        if self.needs_glue(self.node_ty(hid)) {
            return unsup("binding of a value with a destructor in a pattern");
        }
        self.declare_owned(hid, name, m)
    }

    /// As `declare`, for a binding that owns its value, whose destructor `own` arranges.
    fn declare_owned(&mut self, hid: HirId, name: &str, m: hir::Mutability) -> R<Option<String>> {
        // a local with a destructor is dropped by its name, which must not be shadowed while it lives
        if self.drop_scopes.iter().any(|sc| match sc {
            DropScope::Block(ls) | DropScope::Body(ls) => ls.iter().any(|l| l.name == name),
            DropScope::Loop(_) => false,
        }) {
            return unsup("shadowing a local with a destructor");
        }
        let a = if m.is_mut() { self.alloc(self.node_ty(hid))? } else { None };
        self.locals.insert(hid, Local { name: name.to_string(), cell: m.is_mut() });
        Ok(a)
    }

    /// `let [mut] n = v;` for a binding of mutability `m` with the allocator `a` (see `alloc`):
    /// with one from the allocation record, the cell is allocated by calling it.
    fn let_binding(&self, n: &str, m: hir::Mutability, a: &Option<String>, v: &str) -> String {
        match a {
            Some(a) if m.is_mut() => format!("let {} = \\<epsilon>\\<open>{}\\<close>({});", n, a, v),
            _ => format!("let {}{} = {};", m.prefix_str(), n, v),
        }
    }

    // ------------------------------------------------------------------
    // Function bodies
    // ------------------------------------------------------------------

    /// Translate the body of a function; returns (param names, body text).
    pub fn fn_body(&mut self, body: &'tcx hir::Body<'tcx>) -> R<(Vec<String>, String)> {
        self.drop_scopes.push(DropScope::Body(vec![]));
        let r = self.fn_body_scoped(body);
        self.drop_scopes.pop();
        r
    }

    fn fn_body_scoped(&mut self, body: &'tcx hir::Body<'tcx>) -> R<(Vec<String>, String)> {
        let mut params = vec![];
        let mut prologue = vec![];
        for (i, p) in body.params.iter().enumerate() {
            match p.pat.kind {
                PatKind::Binding(bm, hid, ident, None) if let Some(m) = by_value(bm) => {
                    let n = names::local_name(ident.as_str());
                    let n = if params.contains(&n) { format!("{}_{}", n, i) } else { n };
                    params.push(n.clone());
                    let a = self.declare_owned(hid, &n, m)?;
                    if m.is_mut() {
                        prologue.push(self.let_binding(&n, m, &a, &n));
                    }
                    prologue.extend(self.own(hid, true)?);
                }
                _ if self.needs_glue(self.pat_ty(p.pat)) => return unsup("parameter with a destructor bound by a pattern"),
                PatKind::Wild => params.push(format!("unused_{}", i)),
                _ => {
                    let n = format!("arg_{}", i);
                    params.push(n.clone());
                    let lets = self.irrefutable(p.pat, &Tr::atom(n.clone()))?;
                    prologue.extend(lets);
                }
            }
        }
        let b = self.block_expr_inner(body.value)?;
        let b = self.with_body_drops(b)?;
        Ok((params, with_prologue(&prologue, &b)))
    }

    /// The body `b` (statements) of a function or closure followed by the drops of its parameters
    /// (the innermost `Body` scope).
    fn with_body_drops(&mut self, b: String) -> R<String> {
        let Some(DropScope::Body(ls)) = self.drop_scopes.last() else { return Ok(b) };
        let ls = ls.clone();
        let drops = self.drop_locals(&ls)?;
        if drops.is_empty() { return Ok(b) }
        Ok(self.then_drops(&format!("{{\n{}\n}}", b), &drops))
    }

    /// `let r = v; drops; r` (statements, the last the value): Rust computes a block's or a
    /// return's value before the drops.
    fn then_drops(&mut self, v: &str, drops: &[String]) -> String {
        let r = self.fresh("res");
        format!("let {} = {};\n{}\n{}", r, v, drops.join("\n"), r)
    }

    /// Translate an expression used as a whole body (no braces).
    fn block_expr_inner(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<String> {
        match e.kind {
            // `NeverToAny` (of a block of type `!`) does not change the value; `block_seq` handles
            // the divergence inside the block
            ExprKind::Block(b, None) if self.typeck.expr_adjustments(e).iter().all(|a| matches!(a.kind, Adjust::NeverToAny)) => {
                self.block_seq(b.stmts, b.expr)
            }
            // as a block with only this tail (a diverging expression is followed by a panic)
            _ => self.block_seq(&[], Some(e)),
        }
    }

    /// Storage for a mutable local of type `t`: the locale's allocator for its HOL type, which
    /// `let mut` chooses (`None`), or for a type with generic parameters, which the locale cannot
    /// have one for, the allocator of the body's allocation record (a marker completed at
    /// emission, see `Frontend::alloc_sites`).
    fn alloc(&mut self, t: Ty<'tcx>) -> R<Option<String>> {
        let (h, modelled) = self.fe.ty_modelled(t);
        if !modelled {
            return unsup(format!("mutable local of the unsupported type `{}`", t));
        }
        if t.walk().any(|g| matches!(g.kind(), ty::GenericArgKind::Type(x) if matches!(x.kind(), ty::Param(_)))) {
            let i = self.fe.alloc_sites.len();
            self.fe.alloc_sites.push((self.key, self.tcx.erase_and_anonymize_regions(t), h));
            return Ok(Some(format!("\u{1}A{}\u{2}", i)));
        }
        self.fe.need_alloc(&h);
        Ok(None)
    }

    // ------------------------------------------------------------------
    // Blocks and statements
    // ------------------------------------------------------------------

    /// A block: its locals with destructors are dropped where it ends (see `DropScope`).
    fn block_seq(&mut self, stmts: &'tcx [hir::Stmt<'tcx>], tail: Option<&'tcx hir::Expr<'tcx>>) -> R<String> {
        self.drop_scopes.push(DropScope::Block(vec![]));
        let r = self.block_seq_inner(stmts, tail);
        self.drop_scopes.pop();
        r
    }

    fn block_seq_inner(&mut self, stmts: &'tcx [hir::Stmt<'tcx>], tail: Option<&'tcx hir::Expr<'tcx>>) -> R<String> {
        let mut parts: Vec<String> = vec![];
        let mut ended_by_divergence = false;
        for (i, st) in stmts.iter().enumerate() {
            match st.kind {
                StmtKind::Item(_) => {}
                StmtKind::Let(l) => {
                    let (pre, post) = self.let_stmt(l)?;
                    let rest = self.block_seq_inner(&stmts[i + 1..], tail)?;
                    parts.push(format!("{}\n{}{}", pre, rest, post));
                    return Ok(join_seq(parts));
                }
                StmtKind::Expr(e) | StmtKind::Semi(e) => {
                    if self.ty_of(e).is_never() {
                        self.diverging(&mut parts, e);
                        ended_by_divergence = true;
                        break;
                    }
                    let s = self.stmt_expr(e);
                    parts.push(s);
                }
            }
        }
        if !ended_by_divergence {
            // the drops of the block's locals, after its value
            let drops = match self.drop_scopes.last() {
                Some(DropScope::Block(ls)) => {
                    let ls = ls.clone();
                    self.drop_locals(&ls)?
                }
                _ => vec![],
            };
            match tail {
                Some(t) if self.ty_of(t).is_never() => self.diverging(&mut parts, t),
                Some(t) => {
                    let tt = self.expr(t);
                    if drops.is_empty() {
                        parts.push(format!("\u{3}{}", tt.s)); // \u{3} marks a tail expression
                    } else {
                        parts.push(format!("\u{3}{}", self.then_drops(&tt.at(20), &drops)));
                    }
                }
                None if !drops.is_empty() => {
                    parts.extend(drops);
                    parts.push("\u{3}()".to_string());
                }
                None => {}
            }
        }
        // a trailing `let _ = e;` (from an expression statement) needs a continuation
        if !ended_by_divergence && tail.is_none() && parts.last().map(|p| p.starts_with("let ")).unwrap_or(false) {
            parts.push("\u{3}()".to_string());
        }
        let s = join_seq(parts);
        Ok(if s.trim().is_empty() { "()".to_string() } else { s })
    }

    /// A statement (or block tail) `e` of type `!`. In uRust a loop, `if` or `match` whose branches
    /// all leave the function still has type `unit`, so the statement is followed by a panic that
    /// is reached only when the fuel of a loop is exhausted. A panic or placeholder becomes the
    /// value of the block.
    fn diverging(&mut self, parts: &mut Vec<String>, e: &'tcx hir::Expr<'tcx>) {
        // the value is discarded: its coercion (`NeverToAny`) does not apply
        let tr = match self.pv_unadj(e) {
            Ok(pv) => self.to_val(pv),
            Err(Unsup(m)) => {
                // the placeholder of an expression of type `!` has any type
                let marker = self.fe.placeholder(&m, Some(e.span));
                let p = self.placeholder_term(&marker, self.ty_of(e));
                parts.push(format!("\u{3}{}", p.s));
                return;
            }
        };
        // a panic (of any type) is the value of the block
        if self.is_std_panic(e) {
            parts.push(format!("\u{3}{}", tr.s));
            return;
        }
        if matches!(e.kind, ExprKind::Ret(_) | ExprKind::Break(..) | ExprKind::Continue(_)) {
            // a `break` with a value, or a jump after drops: its statements (see `stmt_jumps`)
            if let Some(st) = self.stmt_jumps.remove(&e.hir_id) {
                parts.push(format!("\u{4}{}", st));
                return;
            }
            // \u{4}: ends with its own semicolon
            parts.push(if tr.s.ends_with(';') { format!("\u{4}{}", tr.s) } else { format!("{};", tr.s) });
            return;
        }
        // the value is discarded: a panic or `return` inside it has any type, which would be an
        // extra type variable of the definition (a `TYPE` argument of the constant). `!` is
        // `unit` (see `Frontend::ty`); a loop has type `unit` already
        if matches!(e.kind, ExprKind::Loop(..)) {
            parts.push(format!("{};", tr.at(11)));
        } else {
            parts.push(format!("{};", self.never_as(tr, "unit").s));
        }
        parts.push("\u{3}panic!(\"unreachable: diverging expression completed\")".to_string());
    }

    /// The value of an expression of type `!` stated to have the HOL type `h` (the type it is
    /// coerced to; `!` itself is `unit`, see `Frontend::ty`): a panic or `return` in it has any
    /// type, which unless the context fixes it is an extra type variable of the definition (a
    /// `TYPE` argument of the constant).
    fn never_as(&mut self, tr: Tr, h: &str) -> Tr {
        self.typed("never", tr, h)
    }

    /// Is `e` a call of a standard library function that never returns (translated as a panic,
    /// see `panic_or_print`), possibly as the only part of a block (a macro expansion)?
    fn is_std_panic(&self, e: &'tcx hir::Expr<'tcx>) -> bool {
        match e.kind {
            ExprKind::Block(b, None) => match (b.stmts, b.expr) {
                ([], Some(x)) => self.is_std_panic(x),
                ([st], None) => matches!(st.kind, StmtKind::Expr(x) | StmtKind::Semi(x) if self.is_std_panic(x)),
                _ => false,
            },
            ExprKind::Call(callee, _) => match *self.ty_of(callee).kind() {
                ty::FnDef(did, _) => self.fe.is_std(did) && self.tcx.fn_sig(did).skip_binder().output().skip_binder().is_never(),
                _ => false,
            },
            _ => false,
        }
    }

    /// An expression statement of a type other than `!` (see `diverging`).
    fn stmt_expr(&mut self, e: &'tcx hir::Expr<'tcx>) -> String {
        let t = self.ty_of(e);
        let tr = self.expr(e);
        // a value with a destructor (a temporary) is dropped at the end of the statement
        if self.needs_glue(t) {
            let tmp = self.fresh("temp");
            return match self.drop_glue(t, PV::Val(Tr::atom(tmp.clone()))) {
                Ok(g) => format!("let {} = {};\n{}", tmp, tr.at(20), g.join("\n")),
                Err(Unsup(m)) => {
                    let marker = self.fe.placeholder(&m, Some(e.span));
                    format!("let _ = {};", self.placeholder_term(&marker, t).s)
                }
            };
        }
        if t.is_unit() {
            format!("{};", tr.at(11))
        } else {
            format!("let _ = {};", tr.at(20))
        }
    }

    /// A `let` statement as (prefix, suffix): the rest of the block goes in between.
    fn let_stmt(&mut self, l: &'tcx hir::LetStmt<'tcx>) -> R<(String, String)> {
        if let Some(els) = l.els {
            let init = l.init.ok_or(Unsup("let-else without initializer".into()))?;
            let iv = self.scrut(init)?;
            let place = self.scrut_place(init)?;
            let p = self.pat_at(l.pat, place)?;
            let els_s = self.block_seq(els.stmts, els.expr)?;
            if p.conds.is_empty() && p.prologue.is_empty() {
                return Ok((format!("let {} = {} else {{ {} }};", p.pat, iv.at(20), els_s), String::new()));
            }
            let guard = if p.conds.is_empty() { String::new() } else { format!(" if {}", p.conds.join(" && ")) };
            return Ok((
                format!("match {} {{\n  {}{} \\<Rightarrow> {{\n{}", iv.at(20), p.pat, guard, p.prologue.join("\n")),
                format!("\n}},\n  _ \\<Rightarrow> {{ {} }}\n}}", els_s),
            ));
        }
        match l.init {
            None => {
                // `let x;` -- deferred initialisation: model as a mutable local.
                if let PatKind::Binding(hir::BindingMode(hir::ByRef::No, _), hid, ident, None) = l.pat.kind {
                    let n = names::local_name(ident.as_str());
                    let a = self.declare_owned(hid, &n, hir::Mutability::Mut)?;
                    let ht = self.hty(self.node_ty(hid));
                    let v = format!("\\<llangle>undefined :: {}\\<rrangle>", ht);
                    let flag = self.own(hid, false)?;
                    Ok((with_prologue(&[self.let_binding(&n, hir::Mutability::Mut, &a, &v)], &flag.join("\n")), String::new()))
                } else {
                    unsup("let without initializer and with a non-identifier pattern")
                }
            }
            Some(init) => {
                let mut iv = self.expr(init);
                // a variable of type `!` (no coercion of the initializer fixes its type)
                if self.ty_adj(init).is_never() {
                    iv = self.never_as(iv, "unit");
                }
                // `let _ = e;` drops a temporary at once (a place is not moved)
                let it = self.ty_adj(init);
                if matches!(l.pat.kind, PatKind::Wild) && self.needs_glue(it) && !is_place_expr(self.typeck, init) {
                    let tmp = self.fresh("temp");
                    let g = self.drop_glue(it, PV::Val(Tr::atom(tmp.clone())))?;
                    return Ok((format!("let {} = {};\n{}", tmp, iv.at(20), g.join("\n")), String::new()));
                }
                Ok((self.bind_pattern(l.pat, iv)?, String::new()))
            }
        }
    }

    /// `let <pat> = <value>;` for an irrefutable pattern (one or more statements).
    fn bind_pattern(&mut self, pat: &'tcx hir::Pat<'tcx>, v: Tr) -> R<String> {
        match pat.kind {
            PatKind::Binding(bm, hid, ident, None) if let Some(m) = by_value(bm) => {
                let n = names::local_name(ident.as_str());
                let a = self.declare_owned(hid, &n, m)?;
                let flag = self.own(hid, true)?;
                // the allocator of a mutable local is chosen by its type; for a list or an option the
                // initial value (`[]`, `None`, `Vec::with_capacity(n)`, ...) may not fix the element
                // type when the uses that would are placeholders or external, so it is annotated
                let lt = self.node_ty(hid);
                if m.is_mut() && matches!(lt.kind(), ty::Adt(def, _) if matches!(self.fe.std_adt(def.did()), Some("Vec" | "Option"))) {
                    let ht = self.hty(lt);
                    let tv = self.typed("init", v, &ht);
                    return Ok(with_prologue(&[self.let_binding(&n, m, &a, &tv.s)], &flag.join("\n")));
                }
                Ok(with_prologue(&[self.let_binding(&n, m, &a, &v.at(20))], &flag.join("\n")))
            }
            PatKind::Wild => Ok(format!("let _ = {};", v.at(20))),
            // the parts not bound would be dropped (not modelled)
            _ if self.needs_glue(self.pat_ty(pat)) => unsup("destructuring a value with a destructor"),
            _ => {
                let tmp = self.fresh("destr");
                let lets = self.irrefutable(pat, &Tr::atom(tmp.clone()))?;
                Ok(format!("let {} = {};\n{}", tmp, v.at(20), lets.join("\n")))
            }
        }
    }

    /// Destructure an irrefutable pattern by projections. Returns `let` statements.
    /// Is the value `pat` destructures a mutable reference (match ergonomics), so that its parts
    /// are references focused into it (see `place_field`)?
    fn through_mut_ref(&self, pat: &'tcx hir::Pat<'tcx>) -> bool {
        // the implicit dereferences of match ergonomics, with the types before them
        self.typeck
            .pat_adjustments()
            .get(pat.hir_id)
            .is_some_and(|adj| adj.iter().any(|a| matches!(a.source.kind(), ty::Ref(_, _, m) if m.is_mut())))
    }

    fn irrefutable(&mut self, pat: &'tcx hir::Pat<'tcx>, v: &Tr) -> R<Vec<String>> {
        let mut out = vec![];
        match pat.kind {
            PatKind::Wild => {}
            PatKind::Binding(bm, hid, ident, sub) if let Some(m) = by_value(bm) => {
                let n = names::local_name(ident.as_str());
                let a = self.declare(hid, &n, m)?;
                out.push(self.let_binding(&n, m, &a, &v.at(20)));
                if let Some(s) = sub {
                    out.extend(self.irrefutable(s, &Tr::atom(n))?);
                }
            }
            PatKind::Binding(..) => return unsup("`ref mut` binding"),
            PatKind::Tuple(ps, ddpos) => {
                let t = self.pat_ty(pat).peel_refs();
                let through_ref = self.through_mut_ref(pat);
                let n = match t.kind() { ty::Tuple(ts) => ts.len(), _ => ps.len() };
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    if let Some(p) = p {
                        if n > 16 { return unsup("tuple with more than 16 components") }
                        let proj = if through_ref {
                            self.place_field(v, t, k).ok_or_else(|| Unsup("tuple component through a mutable reference".into()))?
                        } else {
                            Tr::new(format!("{}.{}", v.at(998), k), 998)
                        };
                        out.extend(self.irrefutable(p, &proj)?);
                    }
                }
            }
            PatKind::Struct(_, fields, _) => {
                let t = self.pat_ty(pat).peel_refs();
                let ty::Adt(def, _) = t.kind() else { return unsup("struct pattern on non-ADT") };
                if !def.is_struct() || !def.did().is_local() { return unsup("refutable struct pattern in irrefutable position") }
                let adt = def.did();
                let through_ref = self.through_mut_ref(pat);
                for f in fields.iter() {
                    let fidx = self.typeck.field_index(f.hir_id).as_usize();
                    let proj = if through_ref {
                        self.place_field(v, t, fidx).ok_or_else(|| Unsup("field of a recursive struct through a reference".into()))?
                    } else {
                        self.field_read(adt, fidx, v)?
                    };
                    out.extend(self.irrefutable(f.pat, &proj)?);
                }
            }
            PatKind::TupleStruct(_, ps, ddpos) => {
                let t = self.pat_ty(pat).peel_refs();
                let ty::Adt(def, _) = t.kind() else { return unsup("tuple-struct pattern on non-ADT") };
                if !def.is_struct() || !def.did().is_local() { return unsup("refutable tuple-struct pattern in irrefutable position") }
                let adt = def.did();
                let through_ref = self.through_mut_ref(pat);
                let n = def.non_enum_variant().fields.len();
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    if let Some(p) = p {
                        let proj = if through_ref {
                            self.place_field(v, t, k).ok_or_else(|| Unsup("field of a recursive struct through a reference".into()))?
                        } else {
                            self.field_read(adt, k, v)?
                        };
                        out.extend(self.irrefutable(p, &proj)?);
                    }
                }
            }
            PatKind::Ref(p, _, _) | PatKind::Deref(p) => out.extend(self.irrefutable(p, v)?),
            _ => return unsup("pattern in irrefutable position"),
        }
        Ok(out)
    }

    /// A local ADT with no HOL datatype (see `Frontend::opaque_adts`): its values are opaque.
    fn opaque_adt(&self, adt: DefId) -> R<()> {
        if let Some(why) = self.fe.opaque_adts.get(&adt) {
            return unsup(format!("value of the type `{}` ({})", self.tcx.item_name(adt), why));
        }
        Ok(())
    }

    /// Read field `fidx` of the value `v` of the local struct `adt`.
    fn field_read(&mut self, adt: DefId, fidx: usize, v: &Tr) -> R<Tr> {
        self.opaque_adt(adt)?;
        let f = self.fe.field_name(adt, 0, fidx);
        if self.fe.record_adts.contains(&adt) {
            Ok(Tr::new(format!("{}.{}", v.at(99), f), 100))
        } else {
            Ok(Tr::new(format!("\\<llangle>{}\\<rrangle>\\<^sub>1({})", f, v.s), 999))
        }
    }

    // ------------------------------------------------------------------
    // Expressions: values and places
    // ------------------------------------------------------------------

    /// Translate an expression to a value; unsupported constructs become placeholders.
    fn expr(&mut self, e: &'tcx hir::Expr<'tcx>) -> Tr {
        match self.pv_adjusted(e) {
            Ok(pv) => self.to_val(pv),
            Err(Unsup(m)) => {
                let t = self.ty_adj(e);
                let marker = self.fe.placeholder(&m, Some(e.span));
                self.placeholder_term(&marker, t)
            }
        }
    }

    /// The value matched by a pattern: a scrutinee of type `&mut T` (match ergonomics) is
    /// dereferenced; bindings by mutable reference are rejected by the pattern translation.
    fn scrut(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        // a temporary with a destructor lives until the end of the `match` (not modelled)
        if !is_place_expr(self.typeck, e) && self.needs_glue(self.ty_of(e)) {
            return unsup("matching a temporary with a destructor");
        }
        let mut v = self.val(e)?;
        let mut t = self.ty_adj(e);
        while let ty::Ref(_, inner, m) = t.kind() {
            if m.is_mut() {
                v = Tr::new(format!("* {}", v.at(200)), 98);
            }
            t = *inner;
        }
        Ok(v)
    }

    fn val(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let pv = self.pv_adjusted(e)?;
        Ok(self.to_val(pv))
    }

    /// The values of `es`, in order.
    fn vals(&mut self, es: impl IntoIterator<Item = &'tcx hir::Expr<'tcx>>) -> R<Vec<Tr>> {
        es.into_iter().map(|e| self.val(e)).collect()
    }

    fn to_val(&self, pv: PV) -> Tr {
        match pv {
            PV::Val(t) => t,
            PV::Ref(r) => Tr::new(format!("* {}", r.at(200)), 98),
        }
    }

    fn pv_adjusted(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<PV> {
        // a temporary with a destructor that is borrowed: dropped at the end of the statement
        if self.typeck.expr_adjustments(e).iter().any(|a| matches!(a.kind, Adjust::Borrow(_)))
            && !is_place_expr(self.typeck, e)
            && self.needs_glue(self.ty_of(e))
        {
            return unsup("borrowed temporary with a destructor");
        }
        // a place auto-borrowed mutably (a method's receiver, `v[a..b].fill(x)`)
        if self
            .typeck
            .expr_adjustments(e)
            .iter()
            .any(|a| matches!(a.kind, Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut { .. }))))
        {
            self.mark_mut_place(e);
        }
        let mut pv = self.pv_unadj(e)?;
        let mut cur = self.ty_of(e);
        for adj in self.typeck.expr_adjustments(e) {
            let target = self.mono(adj.target);
            pv = match &adj.kind {
                // a `return`, `break` or `continue` is a statement (its block has the value `()`)
                Adjust::NeverToAny if matches!(e.kind, ExprKind::Ret(_) | ExprKind::Break(..) | ExprKind::Continue(_)) => pv,
                Adjust::NeverToAny => {
                    let h = self.hty(target);
                    let v = self.to_val(pv);
                    // a panic has any type; any other expression of type `!` (e.g. a call of a
                    // function returning `!`, whose HOL result is `unit`) is followed by a panic
                    let v = if self.is_std_panic(e) {
                        v
                    } else {
                        let u = self.never_as(v, "unit");
                        Tr::block(format!("{{ {}; panic!(\"unreachable: diverging expression completed\") }}", u.at(11)))
                    };
                    PV::Val(self.never_as(v, &h))
                }
                Adjust::Deref(DerefAdjustKind::Builtin) => self.deref_pv(pv, cur)?,
                // Vec<T> to [T]: the elements
                Adjust::Deref(DerefAdjustKind::Overloaded(_)) if self.is_vec(cur.peel_refs()) && target.peel_refs().is_slice() => {
                    self.vec_elems(pv)
                }
                Adjust::Deref(DerefAdjustKind::Overloaded(_)) => {
                    // Box<T> ~ T, String ~ str ~ byte list
                    let a = self.hty(cur.peel_refs());
                    let b = self.hty(target.peel_refs());
                    if a != b { return unsup(format!("overloaded dereference of `{}`", cur)) }
                    pv
                }
                Adjust::Deref(_) => return unsup("pinned dereference"),
                Adjust::Borrow(AutoBorrow::Ref(m)) => match m {
                    AutoBorrowMutability::Mut { .. } => self.borrow_mut(e, pv, cur)?,
                    AutoBorrowMutability::Not => PV::Val(self.to_val(pv)),
                },
                Adjust::Borrow(_) => return unsup("raw or pinned auto-borrow"),
                Adjust::Pointer(PointerCoercion::Unsize) => {
                    // array -> slice is the identity on lists; a coercion to `dyn Trait` is not
                    if target.walk().any(|g| matches!(g.kind(), ty::GenericArgKind::Type(t) if matches!(t.kind(), ty::Dynamic(..)))) {
                        return unsup("coercion to a trait object");
                    }
                    pv
                }
                Adjust::Pointer(_) => return unsup("pointer coercion"),
                Adjust::GenericReborrow(_) => pv,
            };
            cur = target;
        }
        Ok(pv)
    }

    fn deref_pv(&mut self, pv: PV, ty_before: Ty<'tcx>) -> R<PV> {
        match ty_before.kind() {
            ty::Ref(_, _, m) if m.is_mut() => Ok(PV::Ref(self.to_val(pv))),
            ty::Ref(..) => Ok(PV::Val(self.to_val(pv))),
            ty::Adt(def, _) if def.is_box() => Ok(pv),
            _ => unsup(format!("dereference of `{}`", ty_before)),
        }
    }

    /// Which standard range type `t` is (by lang item), if any.
    fn range_kind(&self, t: Ty<'tcx>) -> Option<RangeKind> {
        let ty::Adt(def, _) = t.kind() else { return None };
        let li = self.tcx.lang_items();
        let d = Some(def.did());
        [
            (li.range_struct(), RangeKind::Range),
            (li.range_inclusive_struct(), RangeKind::Inclusive),
            (li.range_from_struct(), RangeKind::From),
            (li.range_to_struct(), RangeKind::To),
            (li.range_to_inclusive_struct(), RangeKind::ToInclusive),
            (li.range_full_struct(), RangeKind::Full),
        ]
        .into_iter()
        .find(|(item, _)| *item == d)
        .map(|(_, k)| k)
    }

    /// Whether the place `e` is, or lies inside, a subslice `v[a..b]` of a sequence.
    fn in_subslice(&self, mut e: &'tcx hir::Expr<'tcx>) -> bool {
        loop {
            match e.kind {
                ExprKind::Index(b, i, _) => {
                    if self.list_like(self.ty_adj(b).peel_refs()) && self.range_kind(self.ty_adj(i).peel_refs()).is_some() {
                        return true;
                    }
                    e = b;
                }
                ExprKind::Field(b, _) => e = b,
                _ => return false,
            }
        }
    }

    /// `&mut` of a place is the reference to it; `&mut` of a temporary value allocates a
    /// fresh mutable local holding the value (Rust's temporary) and yields its reference.
    fn borrow_mut(&mut self, e: &'tcx hir::Expr<'tcx>, pv: PV, t: Ty<'tcx>) -> R<PV> {
        match pv {
            PV::Ref(r) => Ok(PV::Val(r)),
            // a place in a subslice of a value (not of a place, see `index_place`): the writes
            // through the borrow would be lost
            PV::Val(_) if self.in_subslice(e) => unsup("mutable borrow of a subslice of a value"),
            PV::Val(v) => {
                let a = self.alloc(t)?;
                let tmp = self.fresh("tmp");
                let b = self.let_binding(&tmp, hir::Mutability::Mut, &a, &v.at(20));
                Ok(PV::Val(Tr::block(format!("{{ {} {} }}", b, tmp))))
            }
        }
    }

    /// Marks the indexing expressions of the place `e` (through fields, indexing and
    /// dereferences): a subslice in it is then a reference into the sequence (see `index_place`).
    fn mark_mut_place(&mut self, mut e: &'tcx hir::Expr<'tcx>) {
        loop {
            match e.kind {
                ExprKind::Index(b, _, _) => {
                    self.mut_places.insert(e.hir_id);
                    e = b;
                }
                ExprKind::Field(b, _) | ExprKind::Unary(UnOp::Deref, b) => e = b,
                _ => return,
            }
        }
    }

    /// The fields of the range expression `idx` (`a..b`, `a..`, `..b`, `..=b`, or the unit struct
    /// `..`), with its kind; `None` for other indices (e.g. a variable holding a range).
    fn range_literal(&self, idx: &'tcx hir::Expr<'tcx>) -> Option<(RangeKind, &'tcx [hir::ExprField<'tcx>])> {
        let kind = self.range_kind(self.ty_of(idx))?;
        match idx.kind {
            ExprKind::Struct(_, fields, _) if !matches!(kind, RangeKind::Inclusive) => Some((kind, fields)),
            ExprKind::Path(_) if matches!(kind, RangeKind::Full) => Some((kind, &[])),
            _ => None,
        }
    }

    /// The bounds `(lo, hi, inclusive)` of the range expression `idx` indexing a sequence whose
    /// length is `len` (the end of `a..` and `..`); `None` for other indices (see `range_literal`).
    fn range_bounds(&mut self, idx: &'tcx hir::Expr<'tcx>, len: Tr) -> R<Option<(Tr, Tr, bool)>> {
        let Some((kind, fields)) = self.range_literal(idx) else { return Ok(None) };
        let field = |s: &mut Self, name: rustc_span::Symbol| -> R<Tr> {
            let f = fields.iter().find(|f| f.ident.name == name).expect("range field");
            s.val(f.expr)
        };
        let zero = Tr::atom("0_usize");
        Ok(Some(match kind {
            RangeKind::Range => {
                let lo = field(self, sym::start)?;
                (lo, field(self, sym::end)?, false)
            }
            RangeKind::From => (field(self, sym::start)?, len, false),
            RangeKind::To => (zero, field(self, sym::end)?, false),
            RangeKind::ToInclusive => (zero, field(self, sym::end)?, true),
            RangeKind::Full => (zero, len, false),
            RangeKind::Inclusive => return Ok(None),
        }))
    }

    /// The base of the sequence index `base[..]` as a place: overloaded `Index(Mut)` auto-borrows
    /// the base, so go back to the place through the borrow.
    fn index_base(&mut self, base: &'tcx hir::Expr<'tcx>) -> R<PV> {
        let mut bpv = self.pv_adjusted(base)?;
        let mut bt_adj = self.ty_adj(base);
        while let ty::Ref(_, inner, _) = bt_adj.kind() {
            bpv = self.deref_pv(bpv, bt_adj)?;
            bt_adj = *inner;
        }
        Ok(bpv)
    }

    /// The sequence `base` of `base[..]` as a list place: the elements of a `Vec`.
    fn index_seq(&mut self, base: &'tcx hir::Expr<'tcx>) -> R<PV> {
        let bpv = self.index_base(base)?;
        Ok(if self.is_vec(self.ty_adj(base).peel_refs()) { self.vec_elems(bpv) } else { bpv })
    }

    fn pv_unadj(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<PV> {
        match e.kind {
            ExprKind::Path(ref qp) if let Res::Local(hid) = self.typeck.qpath_res(qp, e.hir_id) => {
                let Some(l) = self.locals.get(&hid).cloned() else {
                    return unsup("use of a captured or unknown local");
                };
                // the value of a local with a destructor moved out: its flag is cleared
                if let Some(f) = self.moved_uses.get(&e.hir_id).cloned() {
                    let read = if l.cell { format!("* {}", l.name) } else { l.name.clone() };
                    let mv = self.fresh("moved");
                    return Ok(PV::Val(Tr::block(format!("{{ let {} = {}; * {} = false; {} }}", mv, read, f, mv))));
                }
                Ok(if l.cell { PV::Ref(Tr::atom(l.name)) } else { PV::Val(Tr::atom(l.name)) })
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                if self.typeck.type_dependent_def_id(e.hir_id).is_some() {
                    // `*v` of a `Vec`: the elements of the place (through the auto-borrow)
                    if self.is_vec(self.ty_adj(inner).peel_refs()) && self.ty_of(e).is_slice() {
                        let p = self.index_base(inner)?;
                        return Ok(self.vec_elems(p));
                    }
                    let a = self.hty(self.ty_adj(inner).peel_refs());
                    let b = self.hty(self.ty_of(e));
                    if a == b { return self.pv_adjusted(inner) }
                    return unsup("overloaded dereference");
                }
                let t = self.ty_adj(inner);
                let p = self.pv_adjusted(inner)?;
                self.deref_pv(p, t)
            }
            ExprKind::Field(base, ident) => {
                if !is_place_expr(self.typeck, base) && self.needs_glue(self.ty_of(base)) {
                    return unsup("field of a temporary with a destructor");
                }
                let bpv = self.pv_adjusted(base)?;
                let bt = self.ty_adj(base);
                match bt.kind() {
                    // the public fields of the range types, read (see `Frontend::ty`): those of a
                    // `Range` (AutoCorrode's `range` record), the only field of `a..` and `..b`
                    ty::Adt(def, _)
                        if let (Some(k @ ("Range" | "RangeFrom" | "RangeTo" | "RangeToInclusive")), PV::Val(v)) = (self.fe.std_adt(def.did()), &bpv) =>
                    {
                        match (k, ident.name) {
                            ("Range", n) if n == sym::start || n == sym::end => {
                                Ok(PV::Val(Tr::new(format!("\\<llangle>range.{}\\<rrangle>\\<^sub>1({})", n, v.s), 999)))
                            }
                            ("RangeFrom", n) if n == sym::start => Ok(PV::Val(v.clone())),
                            ("RangeTo" | "RangeToInclusive", n) if n == sym::end => Ok(PV::Val(v.clone())),
                            _ => unsup(format!("field access on `{}`", bt)),
                        }
                    }
                    ty::Adt(def, _) if def.is_struct() && def.did().is_local() => {
                        let fidx = self.typeck.field_index(e.hir_id).as_usize();
                        let adt = def.did();
                        match bpv {
                            PV::Val(v) => Ok(PV::Val(self.field_read(adt, fidx, &v)?)),
                            PV::Ref(r) => {
                                self.opaque_adt(adt)?;
                                if !self.fe.record_adts.contains(&adt) {
                                    return unsup("field of a recursive struct through a reference");
                                }
                                let f = self.fe.field_name(adt, 0, fidx);
                                Ok(PV::Ref(Tr::new(format!("{}.{}", r.at(99), f), 100)))
                            }
                        }
                    }
                    ty::Tuple(ts) => {
                        let k: usize = ident.as_str().parse().map_err(|_| Unsup("tuple field".into()))?;
                        if ts.len() > 16 { return unsup("tuple with more than 16 components") }
                        match bpv {
                            PV::Val(v) => Ok(PV::Val(Tr::new(format!("{}.{}", v.at(998), k), 998))),
                            PV::Ref(r) => {
                                // the reference to component k, focused like a record field: the
                                // tuple is `t0 × (t1 × (.. × tnil))`, reached by k `snd` lenses and
                                // one `fst` lens
                                let lens = vec!["snd\\<^sub>L"; k]
                                    .into_iter()
                                    .chain(["fst\\<^sub>L"])
                                    .collect::<Vec<_>>()
                                    .join(" \\<circ>\\<^sub>L ");
                                Ok(PV::Ref(Tr::new(
                                    format!("\\<llangle>focus_reference_via_lens ({})\\<rrangle>\\<^sub>1({})", lens, r.s),
                                    999,
                                )))
                            }
                        }
                    }
                    _ => unsup(format!("field access on `{}`", bt)),
                }
            }
            ExprKind::Index(base, idx, _) => {
                let bt = self.ty_adj(base).peel_refs();
                // a sequence indexed by a local type (`impl Index<Var> for Vec<T>`) uses that impl
                let it = self.ty_adj(idx).peel_refs();
                let local_index = matches!(it.kind(), ty::Adt(def, _) if def.did().is_local());
                // a string by a range of byte positions (a value: `&mut str` has no model)
                if self.str_like(bt) && !local_index && !self.mut_places.contains(&e.hir_id) {
                    return self.str_index(base, idx).map(PV::Val);
                }
                if !self.list_like(bt) || local_index {
                    // `base[idx]` on a local type is `*Index::index(&base, idx)`, or
                    // `*IndexMut::index_mut(&mut base, idx)` in a mutable place; the borrow of the
                    // base is its adjustment, the method resolves to the local implementation
                    let local_adt = matches!(bt.kind(), ty::Adt(def, _) if def.did().is_local());
                    if !local_adt && !local_index { return unsup(format!("indexing into `{}`", bt)) }
                    let did = self.typeck.type_dependent_def_id(e.hir_id).expect("overloaded indexing has a method");
                    let gargs = self.node_args(e.hir_id);
                    let argv = self.vals([base, idx])?;
                    let r = self.call_def(did, gargs, argv, &[base, idx], e)?;
                    let is_mut = self.tcx.trait_of_assoc(did) == self.tcx.lang_items().index_mut_trait();
                    return Ok(if is_mut { PV::Ref(r) } else { PV::Val(r) });
                }
                let is_range = self.range_kind(self.ty_adj(idx).peel_refs()).is_some();
                let bpv = self.index_seq(base)?;
                if let PV::Ref(r) = &bpv
                    && let Some(p) = self.index_place(e, base, idx, r)?
                {
                    return Ok(PV::Ref(p));
                }
                // an open range on a value with side effects (`&f()[..6]`): the value is bound first
                if let PV::Val(v) = &bpv
                    && matches!(self.range_literal(idx), Some((RangeKind::From | RangeKind::To | RangeKind::ToInclusive | RangeKind::Full, _)))
                    && !self.is_simple(base)
                {
                    let tmp = self.fresh("base");
                    let bind = format!("let {} = {};", tmp, v.at(20));
                    let Some((lo, hi, incl)) = self.range_bounds(idx, Tr::atom(format!("len({})", tmp)))? else { return unsup("range index") };
                    let sub = format!("{}[{} {} {}]", tmp, lo.at(42), if incl { "..=" } else { ".." }, hi.at(42));
                    return Ok(PV::Val(Tr::block(format!("{{ {} {} }}", bind, sub))));
                }
                let i = match self.open_range(base, idx, &bpv)? {
                    Some(i) => i,
                    None => {
                        // uRust indexes by an integer or a range `a..b`, `a..=b`; other range types
                        // (a `RangeFrom` held in a variable, ...) have no index operation
                        let it = self.ty_adj(idx).peel_refs();
                        if matches!(self.range_kind(it), Some(k) if !matches!(k, RangeKind::Range | RangeKind::Inclusive)) {
                            return unsup(format!("indexing with a range of type `{}`", it));
                        }
                        self.val(idx)?
                    }
                };
                match bpv {
                    PV::Val(v) => Ok(PV::Val(Tr::new(format!("{}[{}]", v.at(100), i.s), 100))),
                    PV::Ref(r) if !is_range => Ok(PV::Ref(Tr::new(format!("{}[{}]", r.at(100), i.s), 100))),
                    PV::Ref(r) => Ok(PV::Val(Tr::new(format!("(* {})[{}]", r.at(200), i.s), 100))),
                }
            }
            _ => Ok(PV::Val(self.val_unadj(e)?)),
        }
    }

    /// `base[idx]` on a string: the bytes of the range `idx`, which must lie within the string and
    /// start and end at character boundaries, else the model panics (see AutoCorrode's
    /// `str_index_range`).
    fn str_index(&mut self, base: &'tcx hir::Expr<'tcx>, idx: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        // the model, `None` for `..` (the whole string)
        let model = match self.range_kind(self.ty_adj(idx).peel_refs()) {
            Some(RangeKind::Range | RangeKind::Inclusive) => Some("str_index_range"),
            Some(RangeKind::From) => Some("str_index_from"),
            Some(RangeKind::To) => Some("str_index_to"),
            Some(RangeKind::ToInclusive) => Some("str_index_to_inclusive"),
            Some(RangeKind::Full) => None,
            None => return unsup(format!("indexing into `{}` with `{}`", self.ty_adj(base).peel_refs(), self.ty_adj(idx))),
        };
        let s = match self.index_base(base)? {
            PV::Val(v) => v,
            PV::Ref(r) => Tr::new(format!("* {}", r.at(200)), 200),
        };
        let Some(model) = model else { return Ok(s) };
        let i = self.val(idx)?;
        Ok(self.named_call(model, vec![s, i]))
    }

    /// `base[idx]` with a range `idx` and the reference `r` to `base` (a sequence): the reference
    /// to the subslice (a focus on the elements between the ones before and the ones after it, see
    /// AutoCorrode's `slice_range_mut`), in a place borrowed mutably or assigned (see
    /// `mark_mut_place`), for an open range on a base with side effects (see `open_range`), and for
    /// a range held in a variable; `None` otherwise (the subslice is a value). A slice keeps its
    /// length, so the focus stays on the elements of the range while the borrow lives.
    fn index_place(&mut self, e: &'tcx hir::Expr<'tcx>, base: &'tcx hir::Expr<'tcx>, idx: &'tcx hir::Expr<'tcx>, r: &Tr) -> R<Option<Tr>> {
        let Some(kind) = self.range_kind(self.ty_adj(idx).peel_refs()) else { return Ok(None) };
        let literal = self.range_literal(idx).is_some() || matches!(kind, RangeKind::Inclusive);
        let open = matches!(kind, RangeKind::From | RangeKind::To | RangeKind::ToInclusive | RangeKind::Full);
        if !(self.mut_places.contains(&e.hir_id) || (open && !self.is_simple(base)) || !literal) {
            return Ok(None);
        }
        let model = match kind {
            RangeKind::Range | RangeKind::Inclusive => "slice_range_mut",
            RangeKind::From => "slice_range_from_mut",
            RangeKind::To => "slice_range_to_mut",
            RangeKind::ToInclusive => "slice_range_to_inclusive_mut",
            // the whole sequence (`..` has no effect)
            RangeKind::Full => return Ok(Some(r.clone())),
        };
        let i = self.val(idx)?;
        Ok(Some(self.named_call(model, vec![r.clone(), i])))
    }

    /// A sequence index `a..`, `..b`, `..=b` or `..` written as the closed uRust range
    /// `a .. len(base)`, `0 .. b`, `0 ..= b`, `0 .. len(base)`. The missing end repeats the base,
    /// so only a base without side effects qualifies; `None` for every other index.
    fn open_range(&mut self, base: &'tcx hir::Expr<'tcx>, idx: &'tcx hir::Expr<'tcx>, bpv: &PV) -> R<Option<Tr>> {
        // `a..b` is a uRust range value; a variable holding a range is not handled here
        if !matches!(self.range_literal(idx), Some((RangeKind::From | RangeKind::To | RangeKind::ToInclusive | RangeKind::Full, _))) {
            return Ok(None);
        }
        if !self.is_simple(base) { return unsup("open range index on a base with side effects") }
        let len = Tr::atom(match bpv {
            PV::Val(v) => format!("len({})", v.at(11)),
            PV::Ref(r) => format!("len(* {})", r.at(200)),
        });
        let Some((lo, hi, incl)) = self.range_bounds(idx, len)? else { return Ok(None) };
        Ok(Some(Tr::new(format!("{} {} {}", lo.at(42), if incl { "..=" } else { ".." }, hi.at(42)), 41)))
    }

    /// The place denoted by an expression; must be a reference.
    fn place(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        self.mark_mut_place(e);
        let mut pv = self.pv_adjusted(e)?;
        // overloaded compound assignment auto-borrows its left-hand side: go back to the place
        let mut t = self.ty_adj(e);
        if matches!(pv, PV::Val(_)) {
            while let ty::Ref(_, inner, m) = t.kind() {
                if !m.is_mut() { break }
                pv = self.deref_pv(pv, t)?;
                t = *inner;
            }
        }
        match pv {
            PV::Ref(r) => Ok(r),
            PV::Val(_) => unsup("assignment to / mutable borrow of a non-mutable place"),
        }
    }

    fn val_unadj(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        match e.kind {
            ExprKind::Lit(lit) => self.lit(&lit.node, self.ty_of(e)),
            ExprKind::Path(ref qp) => self.path_value(qp, e),
            ExprKind::Call(callee, args) => self.call_expr(e, callee, args),
            ExprKind::MethodCall(_, recv, args, _) => {
                let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else {
                    return unsup("unresolved method call");
                };
                let gargs = self.node_args(e.hir_id);
                let arg_exprs: Vec<&'tcx hir::Expr<'tcx>> = std::iter::once(recv).chain(args).collect();
                if let Some(t) = self.fmt_call(did, &arg_exprs, e)? {
                    return Ok(t);
                }
                if let Some(t) = self.encode_utf8_bytes(did, recv)? {
                    return Ok(t);
                }
                let argv = self.vals(arg_exprs.iter().copied())?;
                self.call_def(did, gargs, argv, &arg_exprs, e)
            }
            ExprKind::Tup(es) => {
                if es.is_empty() { return Ok(Tr::atom("()")) }
                if es.len() == 1 { return unsup("1-tuple") }
                let v: R<Vec<String>> = es.iter().map(|x| self.val(x).map(|t| t.at(11))).collect();
                Ok(Tr::new(format!("({})", v?.join(", ")), 998))
            }
            ExprKind::Binary(op, l, r) => self.binary(e, op.node, l, r),
            ExprKind::Unary(UnOp::Not, x) => {
                let xt = self.ty_adj(x).peel_refs();
                if self.typeck.type_dependent_def_id(e.hir_id).is_some() { return self.overloaded_op(e, &[x]) }
                if !(xt.is_bool() || Self::int_suffix(xt).is_some()) { return unsup(format!("`!` on `{}`", xt)) }
                let v = self.val(x)?;
                Ok(Tr::new(format!("!{}", v.at(300)), 300))
            }
            ExprKind::Unary(UnOp::Neg, x) => {
                let xt = self.ty_adj(x).peel_refs();
                if Self::int_suffix(xt).is_none() {
                    if self.typeck.type_dependent_def_id(e.hir_id).is_some() { return self.overloaded_op(e, &[x]) }
                    return unsup(format!("negation of `{}`", xt));
                }
                // a minus sign directly in front of a literal is part of the literal (`-128_i8`)
                if let ExprKind::Lit(hir::Lit { node: LitKind::Int(v, _), .. }) = x.kind {
                    return Self::int_lit(v.get(), true, xt);
                }
                let v = self.val(x)?;
                Ok(Tr::new(format!("-{}", v.at(300)), 300))
            }
            ExprKind::Unary(UnOp::Deref, _) => unreachable!(),
            ExprKind::Cast(x, _) => self.cast(x, self.ty_of(e)),
            ExprKind::Type(x, _) => self.val(x),
            ExprKind::DropTemps(x) => self.val(x),
            ExprKind::If(c, t, el) => self.if_expr(c, t, el),
            ExprKind::Loop(b, label, src, _) => self.loop_expr(e, b, label, src),
            ExprKind::Match(scrut, arms, src) => match src {
                MatchSource::ForLoopDesugar => self.for_loop(scrut, arms),
                MatchSource::TryDesugar(_) => {
                    let ExprKind::Call(_, [inner]) = scrut.kind else { return unsup("`?` desugaring") };
                    if self.exit_after_owned_operand(e) {
                        return unsup("early exit after evaluating a value with a destructor");
                    }
                    let v = self.val(inner)?;
                    // the drops of an early return (see `exit_drops`)
                    let drops = self.exit_drops(None)?;
                    if let Some(t) = self.try_error_conversion(inner, arms, &v, &drops)? {
                        return Ok(t);
                    }
                    if !drops.is_empty() { return unsup("`?` leaving a scope with destructors") }
                    Ok(Tr::new(format!("{}?", v.at(400)), 400))
                }
                MatchSource::Normal | MatchSource::Postfix => self.match_expr(scrut, arms),
                _ => unsup("async/await or format_args"),
            },
            ExprKind::Closure(c) => self.closure(e, c),
            ExprKind::Block(b, label) => {
                if label.is_some() { return unsup("labeled block") }
                let s = self.block_seq(b.stmts, b.expr)?;
                Ok(Tr::block(format!("{{\n{}\n}}", s)))
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let lt = self.ty_of(lhs);
                if self.needs_glue(lt) {
                    // the value, then the place, whose old value is dropped (if a local's flag says
                    // it holds one), then the write
                    let v = self.val(rhs)?;
                    let p = self.place(lhs)?;
                    let (nv, pl) = (self.fresh("new"), self.fresh("place"));
                    let old = self.drop_glue(lt, PV::Ref(Tr::atom(pl.clone())))?;
                    let flag = match lhs.kind {
                        ExprKind::Path(ref qp) => match self.typeck.qpath_res(qp, lhs.hir_id) {
                            Res::Local(h) => self.local_flags.get(&h).cloned(),
                            _ => None,
                        },
                        _ => None,
                    };
                    let (old, set) = match &flag {
                        Some(f) => (format!("if * {} {{\n{}\n}} else {{\n()\n}};", f, old.join("\n")), format!("\n* {} = true;", f)),
                        None => (old.join("\n"), String::new()),
                    };
                    return Ok(Tr::block(format!(
                        "{{\nlet {} = {};\nlet {} = {};\n{}\n* {} = {};{}\n}}",
                        nv,
                        v.at(20),
                        pl,
                        p.at(20),
                        old,
                        pl,
                        nv,
                        set
                    )));
                }
                let p = self.place(lhs)?;
                let v = self.val(rhs)?;
                Ok(Tr::new(format!("* {} = {}", p.at(200), v.at(40)), 40))
            }
            ExprKind::AssignOp(op, lhs, rhs) => self.assign_op(e, op.node, lhs, rhs),
            ExprKind::Field(..) | ExprKind::Index(..) => {
                let pv = self.pv_unadj(e)?;
                Ok(self.to_val(pv))
            }
            ExprKind::AddrOf(hir::BorrowKind::Ref, m, x) => {
                if m.is_mut() {
                    self.mark_mut_place(x);
                    let t = self.ty_adj(x);
                    let pv = self.pv_adjusted(x)?;
                    match self.borrow_mut(x, pv, t)? {
                        PV::Val(v) => Ok(v),
                        PV::Ref(_) => unreachable!(),
                    }
                } else {
                    self.val(x)
                }
            }
            ExprKind::AddrOf(..) => unsup("raw borrow"),
            ExprKind::Break(..) | ExprKind::Continue(_) | ExprKind::Ret(_) if self.exit_after_owned_operand(e) => {
                unsup("early exit after evaluating a value with a destructor")
            }
            ExprKind::Break(dest, None) => self.jump_drops(e, dest, loop_jump("break", dest)),
            // `break v` out of a `loop` producing a value: the loop's result is set (see `loop_expr`)
            ExprKind::Break(dest, Some(v)) => match dest.target_id.ok().and_then(|t| self.loop_results.get(&t).cloned()) {
                Some(res) => {
                    let v = self.val(v)?;
                    // the `break` (with its `;`, of any type) ends the block, which has its type
                    let brk = loop_jump("break", dest).s;
                    let drops = self.exit_drops(dest.target_id.ok())?;
                    let mut st = vec![format!("* {} = {};", res, v.at(40))];
                    st.extend(drops);
                    st.push(brk);
                    Ok(self.jump_stmts(e, st))
                }
                None => unsup("`break` with a value"),
            },
            ExprKind::Continue(dest) => self.jump_drops(e, dest, loop_jump("continue", dest)),
            // the value, then the drops of the locals of the function (or closure)
            ExprKind::Ret(v) => {
                let t = match v {
                    Some(v) => Some(self.val(v)?),
                    None => None,
                };
                let drops = self.exit_drops(None)?;
                if drops.is_empty() {
                    return Ok(Tr::atom(match t {
                        Some(t) => format!("return {};", t.s),
                        None => "return;".to_string(),
                    }));
                }
                let t = t.map(|t| t.at(20)).unwrap_or_else(|| "()".to_string());
                Ok(Tr::atom(format!("return {{\n{}\n}};", self.then_drops(&t, &drops))))
            }
            ExprKind::Struct(qp, fields, tail) => self.struct_expr(e, qp, fields, tail),
            ExprKind::Array(es) => {
                if es.is_empty() { return Ok(Tr::atom("[]")) }
                let v: R<Vec<String>> = es.iter().map(|x| self.val(x).map(|t| t.at(11))).collect();
                Ok(Tr::atom(format!("[{}]", v?.join(", "))))
            }
            ExprKind::Repeat(elem, _) => {
                // `[x; N]` with a known length: the list `replicate N x`, as for `vec![x; n]`
                let ty::Array(_, len) = self.ty_of(e).kind() else { return unsup("array repeat expression") };
                let Some(n) = len.try_to_target_usize(self.tcx) else { return unsup("array repeat expression with a generic length") };
                let x = self.val(elem)?;
                let n = Self::int_lit(n as u128, false, self.tcx.types.usize)?;
                Ok(self.named_call("vec_from_elem", vec![x, n]))
            }
            ExprKind::ConstBlock(..) => unsup("inline const block"),
            ExprKind::InlineAsm(..) => unsup("inline assembly"),
            ExprKind::OffsetOf(..) => unsup("offset_of"),
            ExprKind::Let(..) => unsup("`let` expression outside `if`"),
            ExprKind::Yield(..) => unsup("yield / await"),
            ExprKind::Become(..) => unsup("become"),
            ExprKind::Use(..) => unsup("ergonomic clone `use`"),
            ExprKind::UnsafeBinderCast(..) => unsup("unsafe binder cast"),
            ExprKind::Err(_) => unsup("error expression"),
        }
    }

    // ------------------------------------------------------------------
    // Literals, paths, casts, operators
    // ------------------------------------------------------------------

    /// The uRust literal suffix of an integer type with a model (up to 64 bits).
    fn int_suffix(t: Ty<'tcx>) -> Option<&'static str> {
        Some(match t.kind() {
            ty::Uint(ty::UintTy::U8) => "u8",
            ty::Uint(ty::UintTy::U16) => "u16",
            ty::Uint(ty::UintTy::U32) => "u32",
            ty::Uint(ty::UintTy::U64) => "u64",
            ty::Uint(ty::UintTy::U128) => "u128",
            ty::Uint(ty::UintTy::Usize) => "usize",
            ty::Int(ty::IntTy::I8) => "i8",
            ty::Int(ty::IntTy::I16) => "i16",
            ty::Int(ty::IntTy::I32) => "i32",
            ty::Int(ty::IntTy::I64) => "i64",
            ty::Int(ty::IntTy::I128) => "i128",
            ty::Int(ty::IntTy::Isize) => "isize",
            _ => return None,
        })
    }

    /// The suffix of an integer type, and of `char` the suffix of `u32` (a `char` is its code point,
    /// see `Frontend::ty`): for conversions, which treat a `char` as that integer.
    fn int_or_char_suffix(t: Ty<'tcx>) -> Option<&'static str> {
        if t.is_char() { Some("u32") } else { Self::int_suffix(t) }
    }

    /// An integer type without a uRust model: wider than 64 bits.
    fn unmodelled_int(t: Ty<'tcx>) -> bool {
        t.is_integral() && Self::int_suffix(t).is_none()
    }

    /// The right operand `r` (translated as `rv`, of type `rt`) of a shift: uRust shifts take a
    /// `64 word` amount.
    fn shift_amount(r: &'tcx hir::Expr<'tcx>, rv: Tr, rt: Ty<'tcx>) -> Tr {
        if matches!(rt.kind(), ty::Uint(ty::UintTy::U64 | ty::UintTy::Usize)) {
            return rv;
        }
        match r.kind {
            ExprKind::Lit(hir::Lit { node: LitKind::Int(v, _), .. }) => Tr::atom(format!("{}_u64", v.get())),
            _ => Tr::new(format!("({}) as u64", rv.s), 299),
        }
    }

    /// The literal of magnitude `v`, negated if `neg`, of the integer type `t`.
    fn int_lit(v: u128, neg: bool, t: Ty<'tcx>) -> R<Tr> {
        let Some(sfx) = Self::int_suffix(t) else { return unsup(format!("integer literal of type `{}`", t)) };
        if neg {
            Ok(Tr::new(format!("-{}_{}", v, sfx), 300))
        } else {
            Ok(Tr::atom(format!("{}_{}", v, sfx)))
        }
    }

    /// The literal of the integer type `t` whose bits are `s` (read as two's complement if `t` is signed).
    fn scalar_int_lit(s: ScalarInt, t: Ty<'tcx>) -> R<Tr> {
        let bits = s.to_bits(s.size());
        if t.is_signed() {
            let shift = 128 - s.size().bits();
            let v = (bits as i128) << shift >> shift;
            return Self::int_lit(v.unsigned_abs(), v < 0, t);
        }
        Self::int_lit(bits, false, t)
    }

    fn lit(&mut self, l: &LitKind, t: Ty<'tcx>) -> R<Tr> {
        match l {
            LitKind::Int(v, _) => Self::int_lit(v.get(), false, t),
            LitKind::Bool(b) => Ok(Tr::atom(if *b { "true" } else { "false" })),
            LitKind::Byte(b) => Ok(Tr::atom(format!("{}_u8", b))),
            LitKind::Char(c) => Ok(Tr::atom(format!("\\<llangle>{}\\<rrangle>", hol_char(*c)))),
            LitKind::Str(s, _) => Ok(Tr::atom(format!("\\<llangle>{}\\<rrangle>", hol_str(s.as_str())))),
            LitKind::Float(..) => unsup("floating-point literal"),
            // `b"…"`: the list of its bytes (byte arrays and slices are `8 word list`)
            LitKind::ByteStr(bs, _) => {
                let bytes: Vec<String> = bs.as_byte_str().iter().map(|b| format!("{}_u8", b)).collect();
                Ok(Tr::atom(format!("[{}]", bytes.join(", "))))
            }
            LitKind::CStr(..) => unsup("C string literal"),
            _ => unsup("literal"),
        }
    }

    fn path_value(&mut self, qp: &'tcx hir::QPath<'tcx>, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let res = self.typeck.qpath_res(qp, e.hir_id);
        match res {
            Res::Def(DefKind::Ctor(of, CtorKind::Const), ctor) => {
                let (adt, vidx) = self.ctor_variant(of, ctor);
                self.unit_ctor(adt, vidx)
            }
            Res::SelfCtor(_) => {
                let t = self.ty_of(e);
                let ty::Adt(def, _) = t.kind() else { return unsup("Self constructor") };
                self.unit_ctor(def.did(), 0)
            }
            Res::Def(DefKind::Const | DefKind::AssocConst { .. }, did) | Res::Def(DefKind::Static { .. }, did) => {
                self.const_use(did, e)
            }
            Res::Def(DefKind::Fn | DefKind::AssocFn, _) => self.fn_item_value(e),
            Res::Def(DefKind::Ctor(of, CtorKind::Fn), ctor) => self.ctor_value(of, ctor, e),
            // a const generic parameter in an instance: its value there (an integer or `bool`)
            Res::Def(DefKind::ConstParam, p) if let Inst::Mono(args) = self.key.1 => {
                let i = self.tcx.generics_of(self.key.0).param_def_id_to_index(self.tcx, p).expect("const parameter of the item");
                let t = self.ty_of(e);
                match args.const_at(i as usize).try_to_leaf() {
                    Some(s) if t.is_bool() => Ok(Tr::atom(if s.to_bits(s.size()) != 0 { "true" } else { "false" })),
                    Some(s) if t.is_integral() => Self::scalar_int_lit(s, t),
                    _ => unsup(format!("const generic parameter of type `{}`", t)),
                }
            }
            _ => unsup(format!("path `{}`", self.fe.snippet(e.span))),
        }
    }

    /// The ADT and the variant index of the constructor `ctor`.
    fn ctor_variant(&self, of: CtorOf, ctor: DefId) -> (DefId, usize) {
        let tcx = self.tcx;
        match of {
            CtorOf::Struct => (tcx.parent(ctor), 0),
            CtorOf::Variant => {
                let var = tcx.parent(ctor);
                let adt = tcx.parent(var);
                (adt, tcx.adt_def(adt).variant_index_with_id(var).as_usize())
            }
        }
    }

    fn unit_ctor(&mut self, adt: DefId, vidx: usize) -> R<Tr> {
        self.opaque_adt(adt)?;
        match self.fe.std_adt(adt) {
            Some("Option") => return Ok(Tr::atom("None")),
            Some("FmtError") => return Ok(Tr::atom("fmt_Error")),
            // `..` (see `Frontend::ty`)
            Some("RangeFull") => return Ok(Tr::atom("()")),
            Some("Ordering") => {
                let v = self.tcx.adt_def(adt).variant(vidx.into()).name.to_string();
                return Ok(Tr::atom(format!("Ordering::{}", v)));
            }
            _ => {}
        }
        if !adt.is_local() {
            return match self.fe.ext_ctor(adt, vidx) {
                Some((c, false)) => Ok(Tr::atom(c)),
                _ => unsup("constructor of an external type"),
            };
        }
        Ok(Tr::atom(self.fe.variant_ctor_name(adt, vidx)))
    }

    /// The constant `did` of the integer, `bool` or `char` type `t` as a literal (e.g. `u32::MAX`,
    /// `char::MAX`), if it evaluates to one. A generic constant or a trait's associated constant is
    /// not evaluated (rustc would abort).
    fn scalar_const(&self, did: DefId, t: Ty<'tcx>) -> Option<R<Tr>> {
        let tcx = self.tcx;
        if !(t.is_integral() || t.is_bool() || t.is_char())
            || self.fe.is_trait_item(did)
            || tcx.is_static(did)
            || tcx.generics_of(did).requires_monomorphization(tcx)
        {
            return None;
        }
        let s = tcx.const_eval_poly(did).ok()?.try_to_scalar_int()?;
        Some(if t.is_bool() {
            Ok(Tr::atom(if s.to_bits(s.size()) != 0 { "true" } else { "false" }))
        } else if t.is_char() {
            let c = char::from_u32(s.to_bits(s.size()) as u32).expect("a `char` constant is a Unicode scalar value");
            Ok(Tr::atom(format!("\\<llangle>{}\\<rrangle>", hol_char(c))))
        } else {
            Self::scalar_int_lit(s, t)
        })
    }

    fn const_use(&mut self, did: DefId, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let t = self.ty_of(e);
        if let DefKind::Static { mutability, .. } = self.tcx.def_kind(did)
            && mutability.is_mut()
        {
            return unsup("`static mut`");
        }
        if did.is_local() && self.tcx.hir_maybe_body_owned_by(did.expect_local()).is_some() && !self.fe.is_trait_item(did) {
            self.calls.insert((did, Inst::Generic));
            let m = self.fe.marker((did, Inst::Generic));
            return Ok(Tr::new(format!("\u{1}Z{}\u{2}", m), 999));
        }
        if let Some(lit) = self.scalar_const(did, t) {
            return lit;
        }
        unsup(format!("use of constant `{}`", self.tcx.def_path_str(did)))
    }

    fn cast(&mut self, x: &'tcx hir::Expr<'tcx>, target: Ty<'tcx>) -> R<Tr> {
        let src = self.ty_adj(x);
        // `c as T` is the code point zero-extended or truncated to `T`, and `b as char` (only from
        // `u8`) is the byte zero-extended
        let Some(tsfx) = Self::int_or_char_suffix(target) else { return unsup(format!("`as` cast to `{}`", target)) };
        // `b as T` for `b: bool` is 1 or 0
        if src.is_bool() {
            let b = self.val(x)?;
            return Ok(Tr::new(format!("if {} {{ 1_{} }} else {{ 0_{} }}", b.at(20), tsfx, tsfx), 21));
        }
        if Self::int_or_char_suffix(src).is_none() { return unsup(format!("`as` cast from `{}`", src)) }
        let v = self.val(x)?;
        // `as` binds weaker than unary operators in uRust (precedence 299)
        Ok(Tr::new(format!("({}) as {}", v.s, tsfx), 299))
    }

    fn binop_info(op: BinOpKind) -> (&'static str, u32) {
        // (token, precedence)
        match op {
            BinOpKind::Mul => ("*", 50),
            BinOpKind::Div => ("/", 50),
            BinOpKind::Rem => ("%", 50),
            BinOpKind::Add => ("+", 49),
            BinOpKind::Sub => ("-", 49),
            BinOpKind::Shl => ("<<", 48),
            BinOpKind::Shr => (">>", 48),
            BinOpKind::BitAnd => ("&", 47),
            BinOpKind::BitXor => ("^", 46),
            BinOpKind::BitOr => ("|", 45),
            BinOpKind::Eq => ("==", 44),
            BinOpKind::Ne => ("!=", 44),
            BinOpKind::Lt => ("<", 44),
            BinOpKind::Le => ("<=", 44),
            BinOpKind::Gt => (">", 44),
            BinOpKind::Ge => (">=", 44),
            BinOpKind::And => ("&&", 43),
            BinOpKind::Or => ("||", 42),
        }
    }

    fn mk_bin(op: &str, prec: u32, l: &Tr, r: &Tr) -> Tr {
        // non-atomic operands are always parenthesised: `|` is also closure and pattern syntax,
        // and explicit grouping avoids ambiguous parses
        Tr::new(format!("{} {} {}", l.at(999), op, r.at(999)), prec)
    }

    fn binary(&mut self, e: &'tcx hir::Expr<'tcx>, op: BinOpKind, l: &'tcx hir::Expr<'tcx>, r: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let lt = self.ty_adj(l).peel_refs();
        let rt = self.ty_adj(r).peel_refs();
        if Self::unmodelled_int(lt) || Self::unmodelled_int(rt) {
            return unsup(format!("binary operator on `{}`", if Self::unmodelled_int(lt) { lt } else { rt }));
        }
        let prim = |t: Ty<'tcx>| Self::int_suffix(t).is_some() || t.is_bool() || t.is_char();
        let builtin = self.typeck.type_dependent_def_id(e.hir_id).is_none();
        if !(prim(lt) && prim(rt)) {
            // structural equality on types whose PartialEq is derived (or std); HOL `=` needs
            // both operands at the same HOL type (e.g. not `&str == Cow<str>`)
            if matches!(op, BinOpKind::Eq | BinOpKind::Ne)
                && self.structural_eq(e)
                && self.fe.ty_dry(lt).0 == self.fe.ty_dry(rt).0
            {
                let lv = self.val(l)?;
                let rv = self.val(r)?;
                let (tok, p) = Self::binop_info(op);
                return Ok(Self::mk_bin(tok, p, &lv, &rv));
            }
            if !builtin { return self.overloaded_op(e, &[l, r]) }
            return unsup(format!("binary operator on `{}`", lt));
        }
        let lv = self.val(l)?;
        let rv = self.val(r)?;
        if lt.is_bool() {
            let (tok, p) = Self::bool_binop(op);
            if matches!(op, BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt | BinOpKind::Ge) {
                return unsup("ordering comparison on `bool`");
            }
            return Ok(Self::mk_bin(tok, p, &lv, &rv));
        }
        let rv = if matches!(op, BinOpKind::Shl | BinOpKind::Shr) { Self::shift_amount(r, rv, rt) } else { rv };
        let (tok, p) = Self::binop_info(op);
        Ok(Self::mk_bin(tok, p, &lv, &rv))
    }

    /// Is `==` on this expression structural (derived PartialEq or std impl on structural types)?
    fn structural_eq(&mut self, e: &'tcx hir::Expr<'tcx>) -> bool {
        let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else { return true };
        let args = self.node_args(e.hir_id);
        match self.resolve_instance(did, args) {
            Ok(Some(inst)) => {
                // derived impls, and the std impls (Option, tuples, references, str, slices); not
                // on a type holding a `HashMap`, whose model (a list) has an order
                let rd = inst.def_id();
                self.tcx.impl_of_assoc(rd).is_some()
                    && (self.derived(rd) || self.fe.is_std(rd))
                    && !args.types().any(|t| self.fe.holds_unfaithful_eq(t, &mut HashSet::new()))
            }
            _ => false,
        }
    }

    /// Operator resolved to a trait method (e.g. `impl Add for Point`).
    fn overloaded_op(&mut self, e: &'tcx hir::Expr<'tcx>, operands: &[&'tcx hir::Expr<'tcx>]) -> R<Tr> {
        let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else {
            return unsup("operator on a non-primitive type");
        };
        let args = self.node_args(e.hir_id);
        let argv = self.vals(operands.iter().copied())?;
        self.call_def(did, args, argv, operands, e)
    }

    fn assign_op(&mut self, e: &'tcx hir::Expr<'tcx>, op: hir::AssignOpKind, lhs: &'tcx hir::Expr<'tcx>, rhs: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        use hir::AssignOpKind as A;
        let lt = self.ty_adj(lhs).peel_refs();
        if Self::unmodelled_int(lt) { return unsup(format!("compound assignment on `{}`", lt)) }
        let overloaded = self.typeck.type_dependent_def_id(e.hir_id);
        if !lt.is_integral() && (!lt.is_bool() || overloaded.is_some()) {
            // overloaded compound assignment: call `T::add_assign(&mut lhs, rhs)`
            let Some(did) = overloaded else { return unsup("compound assignment") };
            let args = self.node_args(e.hir_id);
            let p = self.place(lhs)?;
            let v = self.val(rhs)?;
            return self.call_def(did, args, vec![p, v], &[lhs, rhs], e);
        }
        let p = self.place(lhs)?;
        let mut v = self.val(rhs)?;
        if lt.is_bool() {
            let tok = match op { A::BitAndAssign => "&&", A::BitOrAssign => "||", A::BitXorAssign => "!=", _ => return unsup("compound assignment on bool") };
            return Ok(Tr::new(format!("* {} = * {} {} {}", p.at(200), p.at(200), tok, v.at(45)), 40));
        }
        let tok = match op {
            A::AddAssign => "+=",
            A::SubAssign => "-=",
            A::MulAssign => "*=",
            A::RemAssign => "%=",
            A::BitAndAssign => "&=",
            A::BitOrAssign => "|=",
            A::BitXorAssign => "^=",
            A::ShlAssign | A::ShrAssign => {
                v = Self::shift_amount(rhs, v, self.ty_adj(rhs).peel_refs());
                if matches!(op, A::ShlAssign) { "<<=" } else { ">>=" }
            }
            A::DivAssign => {
                // `x /= e` is not in uRust; desugar to `x = *x / e` (the place is evaluated twice,
                // which is only done for places without calls).
                if !self.is_simple(lhs) { return unsup("`/=` on a place with calls") }
                return Ok(Tr::new(format!("* {} = * {} / {}", p.at(200), p.at(200), v.at(51)), 40));
            }
        };
        Ok(Tr::new(format!("* {} {} {}", p.at(200), tok, v.at(40)), 40))
    }

    // ------------------------------------------------------------------
    // Calls
    // ------------------------------------------------------------------

    fn call_expr(&mut self, e: &'tcx hir::Expr<'tcx>, callee: &'tcx hir::Expr<'tcx>, args: &'tcx [hir::Expr<'tcx>]) -> R<Tr> {
        let ExprKind::Path(ref qp) = callee.kind else {
            return unsup("call of a computed function value");
        };
        let res = self.typeck.qpath_res(qp, callee.hir_id);
        match res {
            Res::Def(DefKind::Fn | DefKind::AssocFn, did) => {
                let arg_refs: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
                if let Some(t) = self.fmt_call(did, &arg_refs, e)? {
                    return Ok(t);
                }
                if let Some(t) = self.panic_or_print(did, args, e.span)? {
                    return Ok(t);
                }
                // the instantiation of the callee is part of its type `FnDef(did, args)` (the
                // per-node table has no entry for paths built by desugarings, e.g. of `for`)
                let ty::FnDef(_, gargs) = *self.ty_of(callee).kind() else { return unsup("call target") };
                let gargs = self.tcx.instantiate_bound_regions_with_erased(gargs);
                let arg_exprs: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
                let argv = self.vals(arg_exprs.iter().copied())?;
                self.call_def(did, gargs, argv, &arg_exprs, e)
            }
            Res::Def(DefKind::Ctor(of, CtorKind::Fn), ctor) => {
                let (adt, vidx) = self.ctor_variant(of, ctor);
                let argv = self.vals(args)?;
                self.ctor_call(adt, vidx, argv)
            }
            Res::SelfCtor(_) => {
                let t = self.ty_of(e);
                let ty::Adt(def, _) = t.kind() else { return unsup("Self constructor") };
                let argv = self.vals(args)?;
                self.ctor_call(def.did(), 0, argv)
            }
            Res::Local(hid) => {
                let Some(l) = self.locals.get(&hid).cloned() else { return unsup("call of unknown local") };
                let mut t = self.ty_of(callee);
                // a closure, or a function item (whose value is the closure calling it, see
                // `fn_item_value`), e.g. in an instance at the closure's or function's type
                // or a type parameter bounded by an `Fn` trait (see `Frontend::fn_param_types`)
                let fn_value = match *t.peel_refs().kind() {
                    ty::Closure(..) | ty::FnDef(..) => true,
                    ty::Param(p) => self.fe.fn_params.contains_key(&p.index),
                    _ => false,
                };
                if !fn_value {
                    return unsup("call through a generic `Fn` parameter (trait call in generic code)");
                }
                // the closure value is read out of the local's cell and through the references
                // to it; closures that mutate their captures are not translated (see `closure`), so
                // a call does not change the value
                // (a shared reference is its referent, so only a cell or `&mut` needs a read)
                let mut read = l.cell;
                let mut pv = if l.cell { PV::Ref(Tr::atom(l.name.clone())) } else { PV::Val(Tr::atom(l.name.clone())) };
                while let ty::Ref(_, inner, m) = *t.kind() {
                    read |= m.is_mut();
                    pv = self.deref_pv(pv, t)?;
                    t = inner;
                }
                let fv = self.to_val(pv);
                let argv: Vec<String> = self.vals(args)?.iter().map(|a| a.at(11)).collect();
                if argv.len() > 8 { return unsup("call with more than 8 arguments") }
                let (bind, f) = if !read { (None, l.name) } else {
                    let f = self.fresh("clo");
                    (Some(format!("let {} = {}; ", f, fv.at(20))), f)
                };
                let call = format!("{}({})", f, argv.join(", "));
                Ok(match bind {
                    None => Tr::new(call, 999),
                    Some(b) => Tr::block(format!("{{ {}{} }}", b, call)),
                })
            }
            _ => unsup("call target"),
        }
    }

    // ------------------------------------------------------------------
    // Formatting (`format!`, `write!`): AutoCorrode's `StdLib_Fmt`
    // ------------------------------------------------------------------

    /// The formatting trait `t`, by its name, if it is one (see `Frontend::fmt_traits`).
    fn fmt_trait(&self, t: DefId) -> Option<&str> {
        self.fe.fmt_traits.iter().find(|(d, _)| *d == t).map(|(_, n)| n.as_str())
    }

    fn is_formatter(&self, t: Ty<'tcx>) -> bool {
        matches!(t.peel_refs().kind(), ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("Formatter"))
    }

    /// The model of the formatting trait `tr`'s `fmt` for the primitive type `t` (see `StdLib_Fmt`).
    fn fmt_model(&self, tr: &str, t: Ty<'tcx>) -> Option<String> {
        let kind = match t.kind() {
            ty::Uint(_) => "word",
            ty::Int(_) => "sword",
            ty::Bool => "bool",
            ty::Char => "char",
            _ if self.str_like(t) => "str",
            ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("Utf8Error") => "utf8_error",
            _ => return None,
        };
        let integer = matches!(kind, "word" | "sword");
        let modelled = match tr {
            "Display" | "Debug" => true,
            "LowerHex" | "UpperHex" | "Octal" | "Binary" => integer,
            _ => false,
        };
        modelled.then(|| format!("fmt_{}_{}", tr, kind))
    }

    fn is_fmt_arguments(&self, t: Ty<'tcx>) -> bool {
        matches!(t.kind(), ty::Adt(d, _) if self.tcx.is_lang_item(d.did(), LangItem::FormatArguments))
    }

    /// A call of a standard library function that writes out a `format_args!` expansion:
    /// `alloc::fmt::format` (the `String` it returns, `format!`) and `write_fmt` on a
    /// `Formatter` (`write!(f, …)`, into the formatter).
    fn fmt_call(&mut self, did: DefId, args: &[&'tcx hir::Expr<'tcx>], e: &'tcx hir::Expr<'tcx>) -> R<Option<Tr>> {
        if !self.fe.is_std(did) { return Ok(None) }
        let Some(pos) = args.iter().position(|a| self.is_fmt_arguments(self.ty_of(a))) else { return Ok(None) };
        let out = self.ty_of(e);
        if pos == 0 && args.len() == 1 && matches!(out.kind(), ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("String")) {
            let fa = self.fmt_args(args[0])?;
            let f = self.fresh("fmt");
            self.fe.need_alloc("fmt_Formatter");
            let w = self.fmt_write(&f, &fa)?;
            let r = self.fresh("fmt_r");
            // `alloc::fmt::format` expects the result: an error is a panic
            return Ok(Some(Tr::block(format!(
                "{{ let mut {f} = fmt_formatter_new({FMT_DEFAULT_FLAGS}_u32, 0_u16, 0_u16);\nlet {r} = {w};\nmatch {r} {{\n  Ok(_) \\<Rightarrow> fmt_formatter_buf(* {f}),\n  Err(_) \\<Rightarrow> panic!(\"a formatting trait implementation returned an error when the underlying stream did not\")\n}}\n}}"
            ))));
        }
        if pos == 1 && args.len() == 2 && self.is_formatter(self.ty_of(args[0])) {
            let recv = self.val(args[0])?;
            let fa = self.fmt_args(args[1])?;
            let f = self.fresh("fmt");
            let w = self.fmt_write(&f, &fa)?;
            return Ok(Some(Tr::block(format!("{{ let {} = {};\n{} }}", f, recv.at(20), w))));
        }
        Ok(None)
    }

    /// The parts of a `format_args!` expansion `e`: `fmt::Arguments::from_str(lit)`, or
    /// `{ super let args = (&a, ..); super let args = [rt::Argument::new_display(args.0), ..];
    /// unsafe { fmt::Arguments::new(template, &args) } }`.
    fn fmt_args(&self, e: &'tcx hir::Expr<'tcx>) -> R<FmtArgs<'tcx>> {
        let tcx = self.tcx;
        let e = Self::strip_drop_temps(e);
        let callee_of = |c: &'tcx hir::Expr<'tcx>| match *self.ty_of(c).kind() {
            ty::FnDef(d, _) => Some(d),
            _ => None,
        };
        let on_lang_type = |d: DefId, l: LangItem| {
            tcx.impl_of_assoc(d).is_some_and(|i| matches!(tcx.type_of(i).instantiate_identity().skip_normalization().kind(), ty::Adt(a, _) if tcx.is_lang_item(a.did(), l)))
        };
        match e.kind {
            // a template without placeholders
            ExprKind::Call(c, [lit]) if callee_of(c).is_some_and(|d| on_lang_type(d, LangItem::FormatArguments)) => {
                let ExprKind::Lit(l) = lit.kind else { return unsup("string formatting (format!)") };
                let LitKind::Str(s, _) = l.node else { return unsup("string formatting (format!)") };
                Ok(FmtArgs { vals: vec![], args: vec![], parts: vec![FmtPart::Lit(s.to_string())] })
            }
            ExprKind::Block(b, _) => {
                let ([l1, l2], Some(inner)) = (b.stmts, b.expr) else { return unsup("string formatting (format!)") };
                let (StmtKind::Let(l1), StmtKind::Let(l2)) = (l1.kind, l2.kind) else { return unsup("string formatting (format!)") };
                let (Some(ExprKind::Tup(es)), Some(ExprKind::Array(items))) = (l1.init.map(|x| x.kind), l2.init.map(|x| x.kind)) else {
                    return unsup("string formatting (format!)");
                };
                let vals: Vec<&'tcx hir::Expr<'tcx>> = es
                    .iter()
                    .map(|x| match x.kind {
                        ExprKind::AddrOf(_, hir::Mutability::Not, y) => y,
                        _ => x,
                    })
                    .collect();
                let mut args = vec![];
                for it in items {
                    let ExprKind::Call(c, [fld]) = it.kind else { return unsup("string formatting (format!)") };
                    let Some(ctor) = callee_of(c).filter(|d| on_lang_type(*d, LangItem::FormatArgument)) else {
                        return unsup("string formatting (format!)");
                    };
                    let ExprKind::Field(..) = fld.kind else { return unsup("string formatting (format!)") };
                    args.push((ctor, self.typeck.field_index(fld.hir_id).as_usize()));
                }
                let ExprKind::Block(ub, _) = Self::strip_drop_temps(inner).kind else { return unsup("string formatting (format!)") };
                let Some(ExprKind::Call(c, [tmpl, _])) = ub.expr.map(|x| x.kind) else { return unsup("string formatting (format!)") };
                // `fmt::Arguments::new(template, &args)`
                if !callee_of(c).is_some_and(|d| on_lang_type(d, LangItem::FormatArguments)) {
                    return unsup("string formatting (format!)");
                }
                let ExprKind::Lit(l) = tmpl.kind else { return unsup("string formatting (format!)") };
                let LitKind::ByteStr(bs, _) = l.node else { return unsup("string formatting (format!)") };
                let parts = decode_fmt_template(bs.as_byte_str()).ok_or_else(|| Unsup("string formatting template".into()))?;
                Ok(FmtArgs { vals, args, parts })
            }
            _ => unsup("string formatting (format!)"),
        }
    }

    /// Write the expansion `fa` into the formatter (reference) `f`, like `fmt::write`: the
    /// literal pieces as they are, each placeholder by formatting its argument into a new
    /// formatter with the placeholder's options and writing out that formatter's output. Every
    /// write's error ends the output and is the result, as `?` in `fmt::write`. An expression
    /// of type `fmt::Result`.
    fn fmt_write(&mut self, f: &str, fa: &FmtArgs<'tcx>) -> R<String> {
        let tcx = self.tcx;
        let bad = || Unsup("string formatting template".into());
        let mut pre = vec![];
        let mut names = vec![];
        for v in &fa.vals {
            let n = self.fresh("fa");
            let tv = self.val(v)?;
            pre.push(format!("let {} = {};", n, tv.at(20)));
            names.push(n);
        }
        // `rt::Argument::from_usize` (a dynamic width or precision, the constructor without a
        // trait bound) panics when the value does not fit in `u16`, when the arguments are built
        for &(ctor, t) in &fa.args {
            if self.fmt_arg_trait(ctor).is_none() {
                pre.push(format!("if {} > 65535_usize {{ panic!(\"Formatting argument out of range\") }};", names[t]));
            }
        }
        // the writes in order: statements, and fallible calls (an error is the result)
        enum Step {
            Stmt(String),
            Call(String),
        }
        let mut steps = vec![];
        let mut next = 0usize;
        for part in &fa.parts {
            match part {
                FmtPart::Lit(s) => {
                    steps.push(Step::Call(format!("fmt_write_str({}, \\<llangle>{}\\<rrangle>)", f, hol_str(s))));
                }
                FmtPart::Ph { flags, width, precision, width_arg, precision_arg, arg } => {
                    let i = arg.unwrap_or(next);
                    next = i + 1;
                    let count = |j: &Option<usize>, fixed: u16| -> R<String> {
                        Ok(match j {
                            Some(j) => format!("({}) as u16", names[fa.args.get(*j).ok_or_else(bad)?.1]),
                            None => format!("{}_u16", fixed),
                        })
                    };
                    let (w, p) = (count(width_arg, *width)?, count(precision_arg, *precision)?);
                    let (ctor, t) = *fa.args.get(i).ok_or_else(bad)?;
                    // `rt::Argument::new_debug_noop` formats nothing
                    if tcx.item_name(ctor).as_str() == "new_debug_noop" {
                        continue;
                    }
                    let sub = self.fresh("fmt_arg");
                    self.fe.need_alloc("fmt_Formatter");
                    let call = self.fmt_arg_call(ctor, fa.vals[t], &names[t], &sub)?;
                    steps.push(Step::Stmt(format!("let mut {} = fmt_formatter_new({}_u32, {}, {});", sub, flags, w, p)));
                    steps.push(Step::Call(call));
                    steps.push(Step::Call(format!("fmt_write_codes({}, fmt_formatter_codes(* {}))", f, sub)));
                }
            }
        }
        let e = self.fresh("fmt_e");
        let mut acc = "Ok(())".to_string();
        for step in steps.into_iter().rev() {
            acc = match step {
                Step::Stmt(st) => format!("{}\n{}", st, acc),
                Step::Call(c) => format!("match {} {{\n  Err({}) \\<Rightarrow> Err({}),\n  Ok(_) \\<Rightarrow> {{\n{}\n}}\n}}", c, e, e, acc),
            };
        }
        Ok(format!("{{\n{}\n}}", with_prologue(&pre, &acc)))
    }

    /// The formatting trait bounding the `rt::Argument` constructor `ctor` (`None` for
    /// `from_usize`, a count).
    fn fmt_arg_trait(&self, ctor: DefId) -> Option<DefId> {
        self.tcx.param_env(ctor).caller_bounds().filter_map(|c| c.as_trait_clause().map(|t| t.def_id())).find(|t| self.fmt_trait(*t).is_some())
    }

    /// The call formatting the argument `x` (its value is the local `v`) into the formatter
    /// (reference) `sub`, with the trait that bounds the `rt::Argument` constructor `ctor`: the
    /// trait's `fmt` resolved at the argument's type. The implementations of the formatting
    /// traits for references and `Box` forward to the referent (a `Box<T>` is `T` in HOL, see
    /// `Frontend::ty`), except `Pointer`'s, which print the address.
    fn fmt_arg_call(&mut self, ctor: DefId, x: &'tcx hir::Expr<'tcx>, v: &str, sub: &str) -> R<String> {
        let tcx = self.tcx;
        let Some(tr) = self.fmt_arg_trait(ctor) else { return unsup("string formatting argument without a formatting trait") };
        let mut t = self.ty_of(x);
        if !tcx.is_diagnostic_item(sym::Pointer, tr) {
            loop {
                match t.kind() {
                    ty::Ref(_, _, m) if m.is_mut() => return unsup("formatting a mutable reference"),
                    ty::Ref(_, inner, _) => t = *inner,
                    ty::Adt(d, a) if d.is_box() => t = a.type_at(0),
                    _ => break,
                }
            }
        }
        let Some(fmt_fn) = tcx.associated_items(tr).in_definition_order().find(|i| i.is_fn()).map(|i| i.def_id) else {
            return unsup("formatting trait without `fmt`");
        };
        if let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), args: rargs })) =
            self.resolve_instance(fmt_fn, tcx.mk_args(&[t.into()]))
        {
            if rd.is_local() && self.fe.local_fn_with_body(rd) && !self.derived(rd) {
                return Ok(self.local_call(rd, rargs, vec![Tr::atom(v), Tr::atom(sub)])?.s);
            }
            if self.fe.is_std(rd) && let Some(n) = self.fmt_trait(tr).and_then(|l| self.fmt_model(l, t)) {
                return Ok(format!("{}({}, {})", n, v, sub));
            }
        }
        unsup(format!("formatting a value of type `{}`", t))
    }

    /// Calls of standard library functions recognised before their (`format_args!`) arguments
    /// are translated: a function that never returns is a panic, the only diverging construct
    /// of uRust; a function taking `fmt::Arguments` and returning `()` only produces output,
    /// which is not modelled, so the call is dropped; any other function involving
    /// `fmt::Arguments` formats a string.
    fn panic_or_print(&mut self, did: DefId, args: &'tcx [hir::Expr<'tcx>], sp: Span) -> R<Option<Tr>> {
        let tcx = self.tcx;
        if !self.fe.is_std(did) {
            return Ok(None);
        }
        let sig = tcx.fn_sig(did).instantiate_identity().skip_binder();
        if sig.output().is_never() {
            fn find_str(e: &hir::Expr<'_>) -> Option<String> {
                match e.kind {
                    ExprKind::Lit(l) => match l.node {
                        LitKind::Str(s, _) => Some(s.to_string()),
                        _ => None,
                    },
                    ExprKind::Call(_, a) | ExprKind::Array(a) | ExprKind::Tup(a) => a.iter().find_map(find_str),
                    ExprKind::MethodCall(_, r, a, _) => find_str(r).or_else(|| a.iter().find_map(find_str)),
                    ExprKind::AddrOf(_, _, x) | ExprKind::DropTemps(x) => find_str(x),
                    ExprKind::Block(b, _) => b.expr.and_then(find_str),
                    _ => None,
                }
            }
            let msg = args.iter().find_map(|x| find_str(x)).unwrap_or_else(|| tcx.item_name(did).to_string());
            return Ok(Some(Tr::new(format!("panic!(\"{}\")", names::string_token(&msg)), 999)));
        }
        let fmt_arguments = |t: Ty<'tcx>| {
            t.walk().any(|g| match g.kind() {
                ty::GenericArgKind::Type(x) => {
                    matches!(x.kind(), ty::Adt(d, _) if tcx.is_lang_item(d.did(), LangItem::FormatArguments))
                }
                _ => false,
            })
        };
        if sig.inputs().iter().any(|t| fmt_arguments(*t)) || fmt_arguments(sig.output()) {
            if sig.output().is_unit() {
                let m = self.fe.placeholder("output (print!/println!), dropped", Some(sp));
                self.comments.push(m);
                return Ok(Some(Tr::atom("()")));
            }
            return unsup("string formatting (format!)");
        }
        Ok(None)
    }

    fn ctor_call(&mut self, adt: DefId, vidx: usize, argv: Vec<Tr>) -> R<Tr> {
        self.opaque_adt(adt)?;
        if let Some(k) = self.fe.std_adt(adt) {
            let vname = self.tcx.adt_def(adt).variant(vidx.into()).name.to_string();
            return match (k, vname.as_str()) {
                ("Option", "Some") | ("Result", "Ok") | ("Result", "Err") => {
                    Ok(Tr::new(format!("{}({})", vname, argv[0].at(11)), 999))
                }
                _ => unsup("constructor of a standard library type"),
            };
        }
        if argv.len() > 8 {
            if !adt.is_local() { return unsup("constructor with more than 8 fields") }
            return Ok(self.ctor_many(adt, vidx, argv, vec![]));
        }
        if !adt.is_local() {
            // an external ADT declared with its constructors (see `ExtType::ctors`)
            return match self.fe.ext_ctor(adt, vidx) {
                Some((c, true)) => Ok(self.callee_app(&format!("{}_mk", c), &format!("{}_mk", c), &format!("{}_mk()", c), argv.iter().map(|a| a.at(11)).collect())),
                _ => unsup("constructor of an external type"),
            };
        }
        // `S()`: a constructor without fields has no `_mk` function; it is the value itself
        if argv.is_empty() { return Ok(Tr::atom(self.fe.variant_ctor_name(adt, vidx))) }
        let n = self.fe.variant_call_name(adt, vidx);
        let a: Vec<String> = argv.into_iter().map(|t| t.at(11)).collect();
        Ok(Tr::new(format!("{}({})", n, a.join(", ")), 999))
    }

    /// A local constructor applied to more than 8 values (more than a uRust call or record
    /// expression takes): the values bound in order (after `pre`), then the HOL constructor applied
    /// to them.
    fn ctor_many(&mut self, adt: DefId, vidx: usize, vals: Vec<Tr>, pre: Vec<String>) -> Tr {
        let mut lets = pre;
        let mut names = vec![];
        for v in vals {
            let n = self.fresh("fld");
            lets.push(format!("let {} = {};", n, v.at(20)));
            names.push(n);
        }
        let c = self.fe.variant_ctor_name(adt, vidx);
        Tr::block(format!("{{\n{}\n\\<llangle>{} {}\\<rrangle>\n}}", lets.join("\n"), c, names.join(" ")))
    }

    /// A call of the local function `did` at the generic arguments `args`.
    fn local_call(&mut self, did: DefId, args: GenericArgsRef<'tcx>, argv: Vec<Tr>) -> R<Tr> {
        // (polymorphic recursion is found once the recursive groups are known, see
        // `translate::poly_rec_calls`)
        let (key, kargs) = self.local_callee(did, args)?;
        // a dictionary that cannot be built at this call (e.g. of a derived implementation whose
        // methods have no model): the instance at the call's concrete arguments, which needs none
        let mut key = key;
        let mut dicts = self.callee_dicts(key, kargs);
        if dicts.is_err()
            && key.1 == Inst::Generic
            && !self.fe.is_trait_item(did)
            && !args.has_param()
            && args.types().all(|t| self.fe.ty_dry(t).1)
            && let Some(inst) = self.fe.instance(did, args)
        {
            key = inst;
            dicts = Ok(vec![]);
        }
        let dicts = dicts?;
        self.calls.insert(key);
        let a: Vec<String> = argv.iter().map(|t| t.at(11)).collect();
        // an instance takes neither dictionaries nor an allocation record
        if let Inst::Mono(_) = key.1 {
            let m = self.fe.marker(key);
            return Ok(self.callee_app(&format!("\u{1}C{}\u{2}", m), &format!("\u{1}H{}\u{2}", m), &format!("\u{1}Z{}\u{2}", m), a));
        }
        let i = self.fe.gen_calls.len();
        self.fe.gen_calls.push(GenCall { callee: key, kargs, dicts, args: Some(a) });
        Ok(Tr::new(format!("\u{1}F{}\u{2}", i), 999))
    }

    /// The function translating the local function `did` at the generic arguments `args`, with
    /// the generic arguments of the item its dictionary parameters are the bounds of (see
    /// `Frontend::dict_params`): an instance, the item itself, or for a default method that the
    /// implementation of a type with generic parameters does not override, the method's copy for
    /// that implementation.
    fn local_callee(&mut self, did: DefId, args: GenericArgsRef<'tcx>) -> R<(FnKey<'tcx>, GenericArgsRef<'tcx>)> {
        let Some(key) = self.fe.callee(did, args) else {
            return unsup(format!("more than {} instances of a generic function", crate::frontend::MAX_INSTANCES));
        };
        // a function with const generic parameters is translated only per instance
        if key.1 == Inst::Generic && self.fe.has_const_params(did) {
            return unsup("call of a function with const generic parameters at non-constant arguments");
        }
        if !(self.fe.is_trait_item(did) && key.1 == Inst::Generic) {
            return Ok((key, args));
        }
        let tcx = self.tcx;
        let tr = tcx.trait_of_assoc(did).expect("a default method is a trait item");
        // only the methods that are dictionary fields have copies (see `translate::run`)
        if !self.fe.dict_methods(tr).contains(&did) {
            return unsup("call of a trait default method that is not a dictionary field (with generic parameters of its own, returning `impl Trait`, or with associated types in its signature other than the slots of its dictionaries)");
        }
        let r = ty::TraitRef::new_from_args(tcx, tr, tcx.mk_args(&args[..tcx.generics_of(tr).count()]));
        match self.select(r)? {
            traits::ImplSource::UserDefined(d) if d.impl_def_id.is_local() && !tcx.is_automatically_derived(d.impl_def_id) => {
                Ok((self.fe.impl_copy(did, d.impl_def_id), d.args))
            }
            _ => unsup("call of a trait default method"),
        }
    }

    /// `Instance::try_resolve` in the body's typing environment, with the `impl Trait` types in
    /// `args` revealed (see `select`); arguments that do not normalise there (rustc would abort)
    /// resolve to nothing.
    fn resolve_instance(&self, did: DefId, args: GenericArgsRef<'tcx>) -> Result<Option<ty::Instance<'tcx>>, rustc_span::ErrorGuaranteed> {
        let tcx = self.tcx;
        let env = self.typing_env();
        let args = tcx.erase_and_anonymize_regions(args);
        match crate::frontend::try_normalize(tcx, env, ty::Unnormalized::new_wip(args)) {
            Ok(args) => ty::Instance::try_resolve(tcx, env, did, args),
            Err(_) => Ok(None),
        }
    }

    /// The candidate implementing the trait reference `r` in the body's typing environment (an
    /// `impl Trait` type in it is its hidden type, as for its HOL type, see `Frontend::ty`).
    fn select(&self, r: ty::TraitRef<'tcx>) -> R<&'tcx traits::ImplSource<'tcx, ()>> {
        let tcx = self.tcx;
        let env = self.typing_env();
        let r = tcx.erase_and_anonymize_regions(r);
        let r = crate::frontend::normalize(tcx, env, ty::Unnormalized::new_wip(r));
        tcx.codegen_select_candidate(env.as_query_input(r)).map_err(|_| Unsup(format!("implementation of `{}`", r)))
    }

    /// `f(args)` for the HOL term `f` of a function value.
    fn term_app(&self, f: &str, argv: Vec<Tr>) -> Tr {
        let a: Vec<String> = argv.iter().map(|t| t.at(11)).collect();
        Tr::new(term_call(f, &a), 999)
    }

    // ------------------------------------------------------------------
    // Dictionaries (see `crate::dict`)
    // ------------------------------------------------------------------

    /// The dictionaries `key` takes (see `Frontend::dict_params`), for its bounds at the generic
    /// arguments `kargs` of their item.
    fn callee_dicts(&mut self, key: FnKey<'tcx>, kargs: GenericArgsRef<'tcx>) -> R<Vec<String>> {
        // a parameter of the callee bounded by an `Fn` trait is a function value (see
        // `Frontend::fn_param_types`): its argument must be a closure, a function item, or such a
        // parameter of the body (a function pointer, for one, is a placeholder type)
        let owner = match key.1 {
            Inst::Generic => Some(key.0),
            Inst::ImplCopy(imp) => Some(imp),
            Inst::Mono(_) => None,
        };
        for (i, _, _) in owner.map(|o| self.fe.fn_bounded_params(o)).unwrap_or_default() {
            let fn_value = match *kargs.type_at(i as usize).kind() {
                ty::Closure(..) | ty::FnDef(..) => true,
                ty::Param(p) => self.fe.fn_params.contains_key(&p.index),
                _ => false,
            };
            if !fn_value {
                return unsup(format!("`Fn` parameter of a generic function instantiated with `{}`", kargs.type_at(i as usize)));
            }
        }
        // the callee's signature types are normalised in its own typing environment (its associated
        // types are the variables of its slots, see `translate::slot_tvars`); at the call they must be
        // the types the call has in the body. They need not be: in `fn caller<T: Iterator +
        // IntoIterator>`, `<T as IntoIterator>::Item` is a projection of its own (the bound, not the
        // blanket implementation over `Iterator`), while the callee `fn callee<T: Iterator>(..) -> <T
        // as IntoIterator>::Item` has `<T as Iterator>::Item` through that implementation
        // (a default method's copy: its signature at its implementation's trait reference, and `kargs`
        // the implementation's arguments)
        if !matches!(key.1, Inst::Mono(_)) && matches!(self.tcx.def_kind(key.0), DefKind::Fn | DefKind::AssocFn) {
            let tcx = self.tcx;
            let env = self.typing_env();
            let norm = |x: ty::Unnormalized<'tcx, Ty<'tcx>>| {
                tcx.erase_and_anonymize_regions(crate::frontend::normalize(tcx, env, x))
            };
            let sig = tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(key.0).instantiate_identity().skip_normalization());
            for t in sig.inputs_and_output {
                let declared = match self.fe.inst_args(key) {
                    Some(a) => ty::EarlyBinder::bind(tcx, t).instantiate(tcx, a).skip_normalization(),
                    None => t,
                };
                let callee_view = norm(ty::EarlyBinder::bind(tcx, self.fe.at_key(key, t)).instantiate(tcx, kargs));
                if callee_view != norm(ty::EarlyBinder::bind(tcx, declared).instantiate(tcx, kargs)) {
                    return unsup(format!(
                        "call of a generic function whose signature type `{}` is another type in the callee's typing environment",
                        t
                    ));
                }
            }
        }
        let bounds: Vec<ty::TraitRef<'tcx>> = self.fe.dict_params(key).into_iter().map(|(r, _)| r).collect();
        let mut out = vec![];
        for b in bounds {
            let r = ty::EarlyBinder::bind(self.tcx, b).instantiate(self.tcx, kargs).skip_normalization();
            out.push(paren_term(&self.dict_term(r)?));
        }
        Ok(out)
    }

    /// The dictionary for the trait reference `r` in the body: in a dictionary field, one the field
    /// takes for its method's own bounds (see `impl_dict`); one of the body's dictionary parameters
    /// (or a supertrait's in one), or an implementation's.
    fn dict_term(&mut self, r: ty::TraitRef<'tcx>) -> R<String> {
        for k in 0..self.own_dicts.len() {
            let (p, n) = self.own_dicts[k].clone();
            if let Some(d) = self.bound_dict(p, n, r) {
                return Ok(d);
            }
        }
        match self.select(r)? {
            traits::ImplSource::UserDefined(d) => self.impl_dict(d.impl_def_id, d.args),
            traits::ImplSource::Param(_) => {
                let r = self.tcx.erase_and_anonymize_regions(r);
                let ps = self.dicts.clone();
                ps.into_iter()
                    .find_map(|(p, n)| self.bound_dict(p, n, r))
                    .ok_or_else(|| Unsup(format!("bound `{}` without a dictionary", r)))
            }
            traits::ImplSource::Builtin(..) => self.model_dict(r, "built-in"),
        }
    }

    /// The dictionary of a built-in or derived implementation of `r` (`what`): its methods are
    /// their models (see `model_field`); a method without one makes it a placeholder. The
    /// dictionaries of the supertraits are fields.
    fn model_dict(&mut self, r: ty::TraitRef<'tcx>, what: &str) -> R<String> {
        let tcx = self.tcx;
        let mut fields = vec![];
        for m in self.fe.dict_methods(r.def_id) {
            let Some(f) = self.model_field(r, m) else {
                return unsup(format!("dictionary of the {} implementation of `{}`", what, r));
            };
            let ns = self.own_dict_names(self.fe.own_dict_bounds(m).len());
            fields.push(paren_term(&lambda(&ns, f)));
        }
        for p in self.fe.dict_parents(r.def_id) {
            let p = ty::EarlyBinder::bind(tcx, p).instantiate(tcx, r.args).skip_normalization();
            fields.push(paren_term(&self.dict_term(p)?));
        }
        let name = self.fe.dict_name(r.def_id);
        Ok(if fields.is_empty() { name } else { format!("{} {}", name, fields.join(" ")) })
    }

    /// The model of the method `m` of a derived, built-in or standard-library implementation of
    /// `r`, as a function value, if its direct calls have one: `clone` is the value itself (a value
    /// is its clone), `clone_from` assigns, `eq` and `ne` of a type with itself are HOL
    /// (in)equality (see `binary`, `std_call`); on modelled integers of one type the comparisons and
    /// the arithmetic and bitwise operators (not the shifts, see `shift_amount`) are uRust's, as
    /// `binary` translates them, and `cmp` is AutoCorrode's; on `bool`, `&`, `|`, `^` are as in
    /// `binary`. The methods are identified within their trait, which is a lang or diagnostic item.
    fn model_field(&mut self, r: ty::TraitRef<'tcx>, m: DefId) -> Option<String> {
        let tcx = self.tcx;
        let tr = r.def_id;
        let name = tcx.item_name(m);
        let lam2 = |b: String| format!("\\<lambda>a b. FunctionBody \\<lbrakk> {} \\<rbrakk>", b);
        if tcx.is_lang_item(tr, LangItem::Clone) {
            return match name.as_str() {
                "clone" if self.is_vec(r.self_ty()) => Some("rvec_clone".to_string()),
                "clone" => Some("\\<lambda>x. FunctionBody (literal x)".to_string()),
                "clone_from" => Some("\\<lambda>d s. FunctionBody \\<lbrakk> * d = s; \\<rbrakk>".to_string()),
                _ => None,
            };
        }
        // `Eq`'s hidden `assert_receiver_is_total_eq` (a compile-time check): does nothing
        if tcx.is_diagnostic_item(sym::Eq, tr) && name.as_str() == "assert_receiver_is_total_eq" {
            return Some("\\<lambda>x. FunctionBody (literal ())".to_string());
        }
        let this = r.self_ty();
        let rhs = r.args.types().nth(1);
        let same = rhs.is_some_and(|t| self.fe.ty_dry(t).0 == self.fe.ty_dry(this).0);
        if tcx.is_lang_item(tr, LangItem::PartialEq) && same {
            let call = self.translated_eq(this, Tr::atom("a"), Tr::atom("b")).ok().flatten();
            if let Some(c) = call {
                return match name.as_str() {
                    "eq" => Some(lam2(c.s)),
                    "ne" => Some(lam2(format!("!{}", c.at(300)))),
                    _ => None,
                };
            }
        }
        if tcx.is_lang_item(tr, LangItem::PartialEq) && same && self.vec_of_hol_eq(this) {
            return match name.as_str() {
                "eq" => Some("rvec_eq".into()),
                "ne" => Some("rvec_ne".into()),
                _ => None,
            };
        }
        if tcx.is_lang_item(tr, LangItem::PartialEq) && same && !self.fe.holds_unfaithful_eq(this, &mut HashSet::new()) {
            return match name.as_str() {
                "eq" => Some(lam2("a == b".into())),
                "ne" => Some(lam2("a != b".into())),
                _ => None,
            };
        }
        let int = Self::int_suffix(this).is_some() && rhs.is_none_or(|t| t == this);
        // a `char` is compared by its code point (a `32 word`)
        let char_cmp = this.is_char() && rhs.is_none_or(|t| t == this);
        if (int || char_cmp) && tcx.is_diagnostic_item(sym::Ord, tr) && name.as_str() == "cmp" {
            return Some(lam2("cmp(a, b)".into()));
        }
        let op = Self::trait_binop(tcx, tr, name.as_str())?;
        let comparison = matches!(op, BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt | BinOpKind::Ge);
        if (int && !matches!(op, BinOpKind::Shl | BinOpKind::Shr)) || (char_cmp && comparison) {
            return Some(lam2(format!("a {} b", Self::binop_info(op).0)));
        }
        if this.is_bool() && rhs == Some(this) && matches!(op, BinOpKind::BitAnd | BinOpKind::BitOr | BinOpKind::BitXor) {
            return Some(lam2(format!("a {} b", Self::bool_binop(op).0)));
        }
        None
    }

    /// The binary operator the method `m` of the operator or comparison trait `tr` (a lang item)
    /// implements.
    fn trait_binop(tcx: TyCtxt<'tcx>, tr: DefId, m: &str) -> Option<BinOpKind> {
        use BinOpKind as K;
        let ops = [
            (LangItem::Add, "add", K::Add),
            (LangItem::Sub, "sub", K::Sub),
            (LangItem::Mul, "mul", K::Mul),
            (LangItem::Div, "div", K::Div),
            (LangItem::Rem, "rem", K::Rem),
            (LangItem::BitAnd, "bitand", K::BitAnd),
            (LangItem::BitOr, "bitor", K::BitOr),
            (LangItem::BitXor, "bitxor", K::BitXor),
            (LangItem::Shl, "shl", K::Shl),
            (LangItem::Shr, "shr", K::Shr),
            (LangItem::PartialOrd, "lt", K::Lt),
            (LangItem::PartialOrd, "le", K::Le),
            (LangItem::PartialOrd, "gt", K::Gt),
            (LangItem::PartialOrd, "ge", K::Ge),
        ];
        ops.into_iter().find(|(l, n, _)| tcx.is_lang_item(tr, *l) && *n == m).map(|(_, _, k)| k)
    }

    /// The uRust operator (with its precedence) of `&`, `|`, `^` on `bool`, and of the comparisons.
    fn bool_binop(op: BinOpKind) -> (&'static str, u32) {
        match op {
            BinOpKind::BitAnd => ("&&", 43),
            BinOpKind::BitOr => ("||", 42),
            BinOpKind::BitXor => ("!=", Self::binop_info(op).1),
            _ => Self::binop_info(op),
        }
    }

    /// The dictionary for `r` in the dictionary `d` for the bound `p`: `d` itself, or a
    /// supertrait field of it (transitively).
    fn bound_dict(&mut self, p: ty::TraitRef<'tcx>, d: String, r: ty::TraitRef<'tcx>) -> Option<String> {
        // compared as `select` sees `r`: normalised in the body's typing environment
        let tcx = self.tcx;
        let norm = |x: ty::TraitRef<'tcx>| {
            let x = tcx.erase_and_anonymize_regions(x);
            crate::frontend::normalize(tcx, self.typing_env(), ty::Unnormalized::new_wip(x))
        };
        if norm(p) == norm(r) {
            return Some(d);
        }
        for (k, q) in self.fe.dict_parents(p.def_id).into_iter().enumerate() {
            let q = ty::EarlyBinder::bind(self.tcx, q).instantiate(self.tcx, p.args).skip_normalization();
            let f = self.fe.dict_parent_field(p.def_id, k);
            if let Some(t) = self.bound_dict(q, format!("{} {}", f, paren_term(&d)), r) {
                return Some(t);
            }
        }
        None
    }

    /// The dictionary of the implementation `imp` at the generic arguments `args`: its methods
    /// (a local implementation's translated methods or default-method copies, an external one's
    /// templates), then the dictionaries of the trait's supertraits.
    fn impl_dict(&mut self, imp: DefId, args: GenericArgsRef<'tcx>) -> R<String> {
        let tcx = self.tcx;
        let r = tcx.impl_trait_ref(imp).instantiate(tcx, args).skip_normalization();
        if imp.is_local() && tcx.is_automatically_derived(imp) {
            return self.model_dict(r, "derived");
        }
        let tr = r.def_id;
        let name = self.fe.dict_name(tr);
        let implementors = tcx.impl_item_implementor_ids(imp);
        let mut fields = vec![];
        for m in self.fe.dict_methods(tr) {
            // the method's own bounds at `r`, whose dictionaries the field takes
            let margs = ty::GenericArgs::for_item(tcx, m, |p, _| {
                if (p.index as usize) < r.args.len() { r.args[p.index as usize] } else { tcx.lifetimes.re_erased.into() }
            });
            let own = self.fe.own_dict_bounds(m);
            let ns = self.own_dict_names(own.len());
            let depth = self.own_dicts.len();
            for (b, n) in own.into_iter().zip(&ns) {
                let b = tcx.erase_and_anonymize_regions(ty::EarlyBinder::bind(tcx, b).instantiate(tcx, margs).skip_normalization());
                self.own_dicts.push((b, n.clone()));
            }
            let f = self.impl_field(imp, args, r, m, &implementors);
            self.own_dicts.truncate(depth);
            fields.push(paren_term(&lambda(&ns, f?)));
        }
        for p in self.fe.dict_parents(tr) {
            let p = ty::EarlyBinder::bind(tcx, p).instantiate(tcx, r.args).skip_normalization();
            fields.push(paren_term(&self.dict_term(p)?));
        }
        Ok(if fields.is_empty() { name } else { format!("{} {}", name, fields.join(" ")) })
    }

    /// `n` fresh names for the dictionaries of the own bounds of a trait method that its field takes
    /// (see `impl_dict`).
    fn own_dict_names(&mut self, n: usize) -> Vec<String> {
        (0..n)
            .map(|_| {
                self.fresh += 1;
                format!("od{}", self.fresh)
            })
            .collect()
    }

    /// The value of the field for the method `m` of the dictionary of the implementation `imp` at
    /// `args` (of the trait reference `r`), see `impl_dict`.
    fn impl_field(
        &mut self,
        imp: DefId,
        args: GenericArgsRef<'tcx>,
        r: ty::TraitRef<'tcx>,
        m: DefId,
        implementors: &rustc_hir::def_id::DefIdMap<DefId>,
    ) -> R<String> {
        let tcx = self.tcx;
        Ok(match implementors.get(&m) {
            Some(&im) if imp.is_local() => {
                let iargs = ty::GenericArgs::for_item(tcx, im, |p, _| {
                    if (p.index as usize) < args.len() { args[p.index as usize] } else { tcx.lifetimes.re_erased.into() }
                });
                self.fn_value((im, Inst::Generic), iargs)?
            }
            // a standard-library implementation's method is its model, if it has one, as in
            // direct calls (see `std_call`); other external ones are templates
            Some(&im) => match self.fe.is_std(imp).then(|| self.model_field(r, m)).flatten() {
                Some(f) => f,
                None => self.fe.ext_fun(im, false),
            },
            None if imp.is_local() && m.is_local() => {
                let key = self.fe.impl_copy(m, imp);
                self.fn_value(key, args)?
            }
            None => match self.fe.is_std(imp).then(|| self.model_field(r, m)).flatten() {
                Some(f) => f,
                None => self.fe.ext_fun(m, false),
            },
        })
    }

    /// The local function `key` as a HOL function value, applied to its dictionaries for its
    /// bounds at the generic arguments `kargs` of their item.
    fn fn_value(&mut self, key: FnKey<'tcx>, kargs: GenericArgsRef<'tcx>) -> R<String> {
        let dicts = self.callee_dicts(key, kargs)?;
        self.calls.insert(key);
        let i = self.fe.gen_calls.len();
        self.fe.gen_calls.push(GenCall { callee: key, kargs, dicts, args: None });
        Ok(format!("\u{1}V{}\u{2}", i))
    }

    /// A call of the trait method `did` (at `gargs`) of a bound of the body: the method's field of
    /// the bound's dictionary.
    fn dict_call(&mut self, did: DefId, gargs: GenericArgsRef<'tcx>, argv: Vec<Tr>, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let tcx = self.tcx;
        let c = tcx.generics_of(did).own_counts();
        if c.types > 0 || c.consts > 0 {
            return unsup("call of a trait method with generic parameters of its own in generic code (a dictionary field cannot be polymorphic)");
        }
        let tr = tcx.trait_of_assoc(did).expect("a trait method");
        let r = ty::TraitRef::new_from_args(tcx, tr, tcx.mk_args(&gargs[..tcx.generics_of(tr).count()]));
        if !self.fe.has_dict(tr) {
            return unsup("trait method call in generic code (a trait without dictionaries)");
        }
        if !self.fe.dict_methods(tr).contains(&did) {
            return unsup("call of a trait method that is not a dictionary field (it returns `impl Trait`, has associated types in its signature other than the slots of its dictionaries, or is an internal method of the standard library) in generic code");
        }
        let mut f = format!("{} {}", self.fe.dict_field(tr, did), paren_term(&self.dict_term(r)?));
        for b in self.fe.own_dict_bounds(did) {
            let b = ty::EarlyBinder::bind(tcx, b).instantiate(tcx, gargs).skip_normalization();
            f.push(' ');
            f.push_str(&paren_term(&self.dict_term(b)?));
        }
        let call = self.term_app(&f, argv);
        Ok(self.result_stated(did, call, e))
    }

    fn callee_app(&self, callee: &str, hol: &str, zero: &str, a: Vec<String>) -> Tr {
        if a.is_empty() {
            Tr::new(zero.to_string(), 999)
        } else if a.len() <= 8 {
            Tr::new(format!("{}({})", callee, a.join(", ")), 999)
        } else {
            let wrapped: Vec<String> = a.iter().map(|x| format!("\\<lbrakk>{}\\<rbrakk>", x)).collect();
            Tr::atom(format!("\\<epsilon>\\<open>funcall{} {} {}\\<close>", a.len(), hol, wrapped.join(" ")))
        }
    }

    fn named_call(&self, name: &str, argv: Vec<Tr>) -> Tr {
        let a: Vec<String> = argv.into_iter().map(|t| t.at(11)).collect();
        self.callee_app(name, name, &format!("{}()", name), a)
    }

    fn call_def(
        &mut self,
        did: DefId,
        gargs: GenericArgsRef<'tcx>,
        argv: Vec<Tr>,
        arg_exprs: &[&'tcx hir::Expr<'tcx>],
        e: &'tcx hir::Expr<'tcx>,
    ) -> R<Tr> {
        if argv.len() > 16 { return unsup("call with more than 16 arguments") }
        if self.tcx.fn_sig(did).skip_binder().c_variadic() {
            return unsup("call of a C-variadic function");
        }
        if self.fe.local_fn_with_body(did) && !self.fe.is_trait_item(did) {
            let call = self.local_call(did, gargs, argv)?;
            return Ok(self.result_stated(did, call, e));
        }
        // trait methods: resolve to the implementation (in an instance, at its concrete types)
        let mut target = did;
        if self.tcx.trait_of_assoc(did).is_some() {
            let targs = match self.resolve_instance(did, gargs) {
                Ok(Some(inst)) => match inst.def {
                    ty::InstanceKind::Item(rd) => {
                        target = rd;
                        inst.args
                    }
                    ty::InstanceKind::Virtual(..) => return unsup("dynamic dispatch (trait object)"),
                    _ => {
                        // compiler-generated shims, e.g. `Clone` for primitive/tuple types
                        if let Some(t) = self.std_call(did, did, gargs, &argv, arg_exprs, e)? { return Ok(t) }
                        return unsup(format!("call of `{}`", self.tcx.def_path_str(did)));
                    }
                },
                // a method of a bound of a generic body: no implementation is known
                _ => return self.dict_call(did, gargs, argv, e),
            };
            if target.is_local() && !self.derived(target) {
                let call = self.local_call(target, targs, argv)?;
                return Ok(self.result_stated(target, call, e));
            }
        }
        // functions declared in `extern` blocks: emit a foreign template definition
        if self.tcx.is_foreign_item(target) {
            let n = self.fe.ext_fun(target, true);
            return Ok(self.named_call(&n, argv));
        }
        // methods of types with interior mutability cannot be modelled by values
        let receiver = arg_exprs.first().map(|a| self.ty_adj(a));
        for t in receiver.into_iter().chain([self.ty_of(e)]) {
            let t = t.peel_refs();
            if self.fe.interior_mutable(t, self.typing_env()) {
                return unsup(format!("interior mutability (`{}`)", t));
            }
        }
        // a standard library function could drop a value with a destructor it is given (only
        // `mem::drop`, `swap`, `replace` are known)
        let owned_or_mut = |s: &Self, a: &hir::Expr<'tcx>| {
            let mut t = s.ty_adj(a);
            while let ty::Ref(_, inner, m) = *t.kind() {
                // through a shared reference nothing can be dropped
                if !m.is_mut() { return false }
                t = inner;
            }
            s.needs_glue(t)
        };
        if arg_exprs.iter().any(|a| owned_or_mut(self, a))
            && !matches!(self.std_fn(target), Some(StdFn::Drop | StdFn::Model("mem_swap" | "mem_replace")))
        {
            return unsup("standard library function given a value with a destructor");
        }
        if let Some(t) = self.std_call(did, target, gargs, &argv, arg_exprs, e)? {
            return Ok(self.result_stated(target, t, e));
        }
        if target.is_local() && !self.fe.bodiless_intrinsic(target) {
            return unsup(format!("call of `{}`", self.tcx.def_path_str(target)));
        }
        let n = self.fe.ext_fun(target, false);
        let call = self.named_call(&n, argv);
        Ok(self.result_stated(target, call, e))
    }

    /// The call `call` of `target`, with the known type of its result stated when a type variable
    /// of the result occurs in no parameter (e.g. of `into`, `collect`, or a method of
    /// `impl<T> Static<Option<T>> for On`): the call does not determine it.
    fn result_stated(&mut self, target: DefId, call: Tr, e: &hir::Expr<'tcx>) -> Tr {
        let t = self.ty_of(e);
        // an `impl Trait` type is not stated: its HOL type may differ from the callee's result type
        let unstated = has_opaque(t);
        // `e` is the call itself, not an operator expression resolved to it (e.g. an overloaded
        // index, whose type is that of the place, not of the reference `index_mut` returns)
        let is_call = matches!(e.kind, ExprKind::Call(..) | ExprKind::MethodCall(..));
        if is_call && self.result_undetermined(target) && !t.is_never() && !unstated {
            let h = self.hty(t);
            return self.typed("res", call, &h);
        }
        call
    }

    /// Does the result type of the signature of `did` contain a type parameter that occurs in no
    /// parameter type, or a projection (both are type variables of its template)?
    fn result_undetermined(&self, did: DefId) -> bool {
        let sig = self.tcx.fn_sig(did).instantiate_identity().skip_binder();
        let mut in_inputs = vec![];
        for t in sig.inputs() {
            self.hol_params(*t, &mut in_inputs);
        }
        let mut out = vec![];
        self.hol_params(sig.output(), &mut out);
        out.iter().any(|x| matches!(x.kind(), ty::Alias(..)) || !in_inputs.contains(x))
    }

    /// The type parameters and projections in `t` that its HOL type keeps: a standard ADT modelled
    /// by a HOL type (see `Frontend::ty`) keeps only some of its arguments, e.g. `Vec<T, A>` is
    /// `T list`, so that the allocator `A` of an argument determines nothing; a raw pointer keeps
    /// none.
    fn hol_params(&self, t: Ty<'tcx>, out: &mut Vec<Ty<'tcx>>) {
        let mut w = t.walk();
        while let Some(g) = w.next() {
            let ty::GenericArgKind::Type(x) = g.kind() else { continue };
            match x.kind() {
                ty::Param(_) | ty::Alias(..) => {
                    w.skip_current_subtree();
                    out.push(x);
                }
                // placeholder types without arguments (see `Frontend::ty`)
                ty::RawPtr(..) | ty::FnPtr(..) | ty::Dynamic(..) => w.skip_current_subtree(),
                ty::Adt(def, args) => {
                    let Some(kept) = self.fe.hol_kept_args(def.did()) else { continue };
                    w.skip_current_subtree();
                    for a in args.types().take(kept) {
                        self.hol_params(a, out);
                    }
                }
                _ => {}
            }
        }
    }

    /// Which of the standard library functions with a uRust counterpart `did` is: by its own lang or
    /// diagnostic item, or else as a method of an owner the compiler identifies (a conversion trait
    /// by its diagnostic item, or the type of an inherent impl: a standard ADT by its lang or
    /// diagnostic item, a slice, an unsigned integer). Only the standard library has inherent
    /// impls of primitive types.
    fn std_fn(&self, did: DefId) -> Option<StdFn> {
        let tcx = self.tcx;
        if let Some(&(_, f)) = STD_ITEMS.iter().find(|(i, _)| match *i {
            Item::Lang(l) => tcx.is_lang_item(did, l),
            Item::Diag(s) => tcx.is_diagnostic_item(Symbol::intern(s), did),
        }) {
            return Some(f);
        }
        // the discriminant of an enum (in the derived `PartialEq` of an enum, see
        // `Frontend::translated_derived`)
        if tcx.intrinsic(did).is_some_and(|i| i.name == sym::discriminant_value) {
            return Some(StdFn::DiscriminantValue);
        }
        let parent = tcx.parent(did);
        let owner = match tcx.def_kind(parent) {
            // `Into::into`, `AsRef::as_ref`, `Borrow::borrow` are their traits' only methods
            DefKind::Trait => {
                if self.fmt_trait(parent).is_some() {
                    return Some(StdFn::FmtTrait(parent));
                }
                // `fmt::Write::write_str`, `write_char` (on a `Formatter`, see `std_call`)
                if tcx.is_diagnostic_item(Symbol::intern("FmtWrite"), parent) {
                    return match tcx.item_name(did).as_str() {
                        "write_str" => Some(StdFn::FmtMethod("fmt_write_str")),
                        "write_char" => Some(StdFn::FmtMethod("fmt_write_char")),
                        _ => None,
                    };
                }
                // the methods of `Iterator` with models (on the iterators of `Frontend::iter_step`)
                if tcx.is_diagnostic_item(sym::Iterator, parent) {
                    use IterFn::*;
                    return Some(StdFn::Iter(match tcx.item_name(did).as_str() {
                        "next" => Next,
                        "enumerate" => Enumerate,
                        "zip" => Zip,
                        "skip" => Skip,
                        "take" => Take,
                        "filter" => Filter,
                        "any" => Any,
                        "for_each" => ForEach,
                        "min" => Min,
                        "take_while" => TakeWhile,
                        "map" => Map,
                        "rev" | "copied" | "cloned" => Same,
                        "count" => Count,
                        "collect" => Collect,
                        _ => return None,
                    }));
                }
                if tcx.is_diagnostic_item(sym::TryInto, parent) {
                    return Some(StdFn::TryIntoArray);
                }
                // `String + &str`, `String += &str` (see `std_call`)
                if Some(parent) == tcx.lang_items().add_trait() {
                    return Some(StdFn::StringAdd);
                }
                if Some(parent) == tcx.lang_items().add_assign_trait() {
                    return Some(StdFn::StringAddAssign);
                }
                // `IntoIterator::into_iter` of an iterator, or of a reference to a sequence, whose
                // state is the sequence: the identity when the HOL types agree
                return [sym::Into, sym::AsRef, sym::Borrow, sym::IntoIterator]
                    .into_iter()
                    .any(|t| tcx.is_diagnostic_item(t, parent))
                    .then_some(StdFn::Conversion);
            }
            DefKind::Impl { of_trait: false } => match tcx.type_of(parent).instantiate_identity().skip_normalization().kind() {
                ty::Adt(def, _) => self.fe.std_adt(def.did())?,
                ty::Slice(_) => "slice",
                ty::Str => "str",
                ty::Char => "char",
                ty::Uint(_) => "uint",
                ty::Int(_) => "int",
                _ => return None,
            },
            _ => return None,
        };
        use StdFn::*;
        Some(match (owner, tcx.item_name(did).as_str()) {
            ("Option", "is_some") => OptionIsSome,
            ("Option", "is_none") => OptionIsNone,
            ("Option", "ok_or") => OptionOkOr,
            ("Option", "take") => OptionTake,
            ("Result", "unwrap") => ResultUnwrap,
            ("Result", "expect") => ResultExpect,
            ("Result", "is_ok") => ResultIsOk,
            ("Result", "is_err") => ResultIsErr,
            ("Result", "unwrap_or") => ResultUnwrapOr,
            ("slice", "len") => Len,
            ("slice", "iter_mut") => SliceIterMut,
            // a boxed slice keeps its length as the capacity; a copy gets a new allocation
            ("slice", "into_vec") => VecFromList,
            ("slice", "to_vec") => VecAlloc,
            ("slice", "swap") => SliceSwap,
            ("uint" | "int", "checked_add") => IntOp("checked_add"),
            ("uint" | "int", "checked_mul") => IntOp("checked_mul"),
            ("uint" | "int", "saturating_sub") => IntOp("saturating_sub"),
            ("uint" | "int", "div_ceil") => IntOp("div_ceil"),
            ("int", "wrapping_add_unsigned") => IntOp("wrapping_add_unsigned"),
            // the models of AutoCorrode's `StdLib_Frontend_Models`
            ("Option", "unwrap_or") => Model("option_unwrap_or"),
            ("Option", "unwrap_or_else") => Model("option_unwrap_or_else"),
            ("Option", "map") => Model("option_map"),
            ("Option", "and_then") => Model("option_and_then"),
            ("Option", "is_some_and") => Model("option_is_some_and"),
            ("Option", "ok_or_else") => Model("option_ok_or_else"),
            ("Option", "copied" | "cloned" | "as_ref") => Conversion,
            ("Result", "map") => Model("result_map"),
            ("Result", "map_err") => Model("result_map_err"),
            ("slice", "is_empty") => Model("slice_is_empty"),
            ("slice", "first") => Model("slice_first"),
            ("slice", "last") => Model("slice_last"),
            ("slice", "get") => SliceGet,
            ("slice", "copy_within") => SliceCopyWithin,
            ("Range" | "RangeInclusive", "contains") => RangeContains,
            ("slice", "get_mut") => SliceGetMut,
            ("slice", "chunks_exact") => Model("slice_chunks_exact"),
            ("slice", "chunks") => Model("slice_chunks"),
            ("slice", "copy_from_slice") => Model("slice_copy_from_slice"),
            ("slice", "fill") => Model("slice_fill"),
            ("slice", "reverse") => Model("slice_reverse"),
            // the models of a `Vec` with its capacity (AutoCorrode's `StdLib_Vec`)
            ("Vec", "len") => Model("rvec_len"),
            ("Vec", "is_empty") => Model("rvec_is_empty"),
            ("Vec", "capacity") => Model("rvec_capacity"),
            ("Vec", "push") => Model("rvec_push"),
            ("Vec", "pop") => Model("rvec_pop"),
            ("Vec", "truncate") => Model("rvec_truncate"),
            ("Vec", "clear") => Model("rvec_clear"),
            ("Vec", "resize") => Model("rvec_resize"),
            ("Vec", "extend_from_slice") => Model("rvec_extend_from_slice"),
            ("Vec", "reserve") => Model("rvec_reserve"),
            ("Vec", "reserve_exact") => Model("rvec_reserve_exact"),
            ("Vec", "shrink_to_fit") => Model("rvec_shrink_to_fit"),
            ("Vec", "shrink_to") => Model("rvec_shrink_to"),
            ("Vec", "insert") => Model("rvec_insert"),
            ("Vec", "remove") => Model("rvec_remove"),
            ("Vec", "swap_remove") => Model("rvec_swap_remove"),
            ("Vec", "as_mut_slice") => Model("rvec_as_mut_slice"),
            ("Vec", "into_boxed_slice") => VecElems,
            ("Vec", "dedup") => VecDedup,
            ("slice", "sort") => SliceSort,
            // a hash map whose iteration order is not observed (see `STD_MODELS.md`)
            ("HashMap", "new") => ModelTyped("hashmap_new"),
            ("HashMap", "len") => Model("hashmap_len"),
            ("HashMap", "is_empty") => Model("hashmap_is_empty"),
            ("HashMap", "contains_key") => HashMapKey("hashmap_contains_key"),
            ("HashMap", "get") => HashMapKey("hashmap_get"),
            ("HashMap", "get_mut") => HashMapKey("hashmap_get_mut"),
            ("HashMap", "insert") => HashMapKey("hashmap_insert"),
            ("HashMap", "remove") => HashMapKey("hashmap_remove"),
            ("HashMap", "entry") => HashMapKey("hashmap_entry"),
            ("HashMapEntry", "or_insert") => Model("hashmap_entry_or_insert"),
            // strings: the lists of their UTF-8 bytes, see `Frontend::ty` and AutoCorrode's
            // `StdLib_Utf8`
            ("str" | "String", "len") => Len,
            ("str" | "String", "is_empty") => Model("slice_is_empty"),
            ("String", "new" | "with_capacity") => StringNew,
            ("String", "as_bytes" | "into_boxed_str") => Conversion,
            // a `Vec<u8>` of the bytes, and the string of the bytes of a `Vec<u8>`
            ("String", "into_bytes") => VecAlloc,
            ("String", "from_utf8_unchecked") => VecElems,
            ("String", "push_str") => Model("vec_extend_from_slice"),
            ("String", "push") => Model("string_push"),
            ("String", "pop") => Model("string_pop"),
            ("String", "truncate") => Model("string_truncate"),
            ("String", "clear") => Model("vec_clear"),
            ("str", "lines") => Model("str_lines"),
            ("str", "split_whitespace") => Model("str_split_whitespace"),
            ("str", "chars") => Model("str_chars"),
            ("str", "char_indices") => Model("str_char_indices"),
            // the state of `Bytes` is the string itself
            ("str", "bytes") => Conversion,
            ("str", "as_bytes") => Model("str_as_bytes"),
            ("str", "trim") => Model("str_trim"),
            ("str", "trim_start") => Model("str_trim_start"),
            ("str", "trim_end") => Model("str_trim_end"),
            ("str", "is_char_boundary") => Model("str_is_char_boundary_fn"),
            ("str", "split_at") => Model("str_split_at"),
            ("str", "repeat") => Model("str_repeat"),
            ("str", "get") => StrGet,
            ("str" | "slice", "is_ascii") => Model("bytes_is_ascii"),
            ("str" | "slice", "eq_ignore_ascii_case") => Model("bytes_eq_ignore_ascii_case"),
            ("str" | "slice", "to_ascii_uppercase") => Model("bytes_to_ascii_uppercase"),
            ("str" | "slice", "to_ascii_lowercase") => Model("bytes_to_ascii_lowercase"),
            ("str", "from_utf8") => Model("str_from_utf8"),
            ("str", "from_utf8_unchecked") => Conversion,
            ("String", "from_utf8") => StringFromUtf8,
            ("Utf8Error", "valid_up_to") => Model("utf8_error_valid_up_to_fn"),
            ("Utf8Error", "error_len") => Model("utf8_error_error_len_fn"),
            ("FromUtf8Error", "utf8_error") => Model("from_utf8_error_utf8_error"),
            ("FromUtf8Error", "as_bytes") => Model("from_utf8_error_into_bytes"),
            ("FromUtf8Error", "into_bytes") => FromUtf8ErrorIntoBytes,
            // only followed by `as_bytes` (see `encode_utf8_bytes`)
            ("char", "encode_utf8") => CharEncodeUtf8,
            ("str", "starts_with") => StrPattern("str_starts_with"),
            ("str", "ends_with") => StrPattern("str_ends_with"),
            ("str", "strip_prefix") => StrPattern("str_strip_prefix"),
            ("str", "strip_suffix") => StrPattern("str_strip_suffix"),
            ("str", "contains") => StrPattern("str_contains"),
            ("str", "find") => StrPattern("str_find"),
            ("str", "parse") => StrParse,
            // characters: their code points
            ("char", "len_utf8") => Model("char_len_utf8"),
            ("char", "from_u32") => Model("char_from_u32"),
            ("char", "to_digit") => Model("char_to_digit"),
            ("char", "from_digit") => Model("char_from_digit"),
            ("char", "is_whitespace") => Model("char_is_whitespace_fn"),
            ("char", "is_control") => Model("char_is_control_fn"),
            // the ASCII methods of `u8` and `char` (only `u8` has them among the integers)
            ("char" | "uint", "is_ascii") => AsciiTest("\\<lambda>_. True"),
            ("char" | "uint", "is_ascii_alphabetic") => AsciiTest("ascii_is_alphabetic"),
            ("char" | "uint", "is_ascii_uppercase") => AsciiTest("ascii_is_uppercase"),
            ("char" | "uint", "is_ascii_lowercase") => AsciiTest("ascii_is_lowercase"),
            ("char" | "uint", "is_ascii_alphanumeric") => AsciiTest("ascii_is_alphanumeric"),
            ("char" | "uint", "is_ascii_digit") => AsciiTest("ascii_is_digit"),
            ("char" | "uint", "is_ascii_hexdigit") => AsciiTest("ascii_is_hexdigit"),
            ("char" | "uint", "is_ascii_punctuation") => AsciiTest("ascii_is_punctuation"),
            ("char" | "uint", "is_ascii_graphic") => AsciiTest("ascii_is_graphic"),
            ("char" | "uint", "is_ascii_whitespace") => AsciiTest("ascii_is_whitespace"),
            ("char" | "uint", "is_ascii_control") => AsciiTest("ascii_is_control"),
            ("char" | "uint", "to_ascii_uppercase") => Model("ascii_to_uppercase"),
            ("char" | "uint", "to_ascii_lowercase") => Model("ascii_to_lowercase"),
            ("char" | "uint", "eq_ignore_ascii_case") => Model("ascii_eq_ignore_case"),
            // the type of the result is that of the call
            ("uint", "from_str_radix") => ModelTyped("from_str_radix_word"),
            ("int", "from_str_radix") => ModelTyped("from_str_radix_sword"),
            // bitwise operations: also on signed integers, whose HOL type is a word type
            ("uint" | "int", "wrapping_add") => Model("wrapping_add"),
            ("uint" | "int", "wrapping_sub") => Model("wrapping_sub"),
            ("uint" | "int", "wrapping_mul") => Model("wrapping_mul"),
            ("uint" | "int", "trailing_zeros") => Model("trailing_zeros"),
            ("uint" | "int", "leading_zeros") => Model("leading_zeros"),
            ("uint" | "int", "from_be_bytes") => ModelTyped("from_be_bytes"),
            // the frontend assumes a little-endian platform
            ("uint" | "int", "from_le_bytes" | "from_ne_bytes") => ModelTyped("from_le_bytes"),
            ("uint" | "int", "to_be_bytes") => Model("to_be_bytes"),
            ("uint" | "int", "to_le_bytes" | "to_ne_bytes") => Model("to_le_bytes"),
            ("uint" | "int", "to_le") => Conversion,
            // comparisons: on unsigned integers only (HOL's order of words is unsigned)
            ("uint", "checked_sub") => Model("checked_sub"),
            ("uint", "overflowing_sub") => Model("overflowing_sub"),
            ("uint", "checked_shl") => Model("checked_shl"),
            // the models of AutoCorrode's `StdLib_Fmt`
            ("Formatter", "write_str") => FmtMethod("fmt_write_str"),
            ("Formatter", "write_char") => FmtMethod("fmt_write_char"),
            ("Formatter", "pad") => FmtMethod("fmt_pad"),
            ("Formatter", "pad_integral") => FmtMethod("fmt_pad_integral"),
            ("Formatter", "alternate") => FmtMethod("fmt_alternate"),
            ("Formatter", "sign_plus") => FmtMethod("fmt_sign_plus"),
            ("Formatter", "sign_minus") => FmtMethod("fmt_sign_minus"),
            ("Formatter", "sign_aware_zero_pad") => FmtMethod("fmt_sign_aware_zero_pad"),
            ("Formatter", "width") => FmtMethod("fmt_width"),
            ("Formatter", "precision") => FmtMethod("fmt_precision"),
            ("Formatter", "fill") => FmtMethod("fmt_fill"),
            _ => return None,
        })
    }

    fn std_call(
        &mut self,
        orig: DefId,
        target: DefId,
        gargs: GenericArgsRef<'tcx>,
        argv: &[Tr],
        arg_exprs: &[&'tcx hir::Expr<'tcx>],
        e: &'tcx hir::Expr<'tcx>,
    ) -> R<Option<Tr>> {
        // the table covers standard library functions and derived methods
        if !(self.fe.is_std(target) || self.derived(target)) {
            return Ok(None);
        }
        // `fn<T>(x: T) -> T` without bounds (`hint::must_use`, `convert::identity`,
        // `hint::black_box`): the identity
        if self.fe.is_std(target) && argv.len() == 1 && self.identity_shaped(target) {
            return Ok(Some(argv[0].clone()));
        }
        let Some(f) = self.std_fn(orig) else { return Ok(None) };
        let a = |i: usize| -> Tr { argv[i].clone() };
        let same_hol = |this: &mut Self| -> bool {
            if arg_exprs.is_empty() { return false }
            let src = this.ty_adj(arg_exprs[0]).peel_refs();
            let dst = this.ty_of(e).peel_refs();
            this.fe.ty(src) == this.fe.ty(dst)
        };
        // HOL `=` needs both operands at the same HOL type
        let same_operands = |this: &mut Self| -> bool {
            if arg_exprs.len() != 2 { return false }
            let l = this.ty_adj(arg_exprs[0]).peel_refs();
            let r = this.ty_adj(arg_exprs[1]).peel_refs();
            this.fe.ty_dry(l).0 == this.fe.ty_dry(r).0
        };
        use StdFn::*;
        let r = match f {
            // a `Vec`'s clone is a new allocation (AutoCorrode's `rvec_clone`)
            Clone if self.is_vec(self.ty_adj(arg_exprs[0]).peel_refs()) => Some(self.named_call("rvec_clone", vec![a(0)])),
            Clone => Some(a(0)),
            // a type whose derived `PartialEq` is translated (also through references): its `eq`
            Eq | Ne if same_operands(self) && let Some(c) = self.translated_eq(self.ty_adj(arg_exprs[0]), a(0), a(1))? => {
                Some(if matches!(f, Eq) { c } else { Tr::new(format!("!{}", c.at(300)), 300) })
            }
            // the elements of `Vec`s whose elements HOL's equality compares (not the capacities)
            Eq | Ne if same_operands(self) && self.vec_of_hol_eq(self.ty_adj(arg_exprs[0]).peel_refs()) => {
                Some(self.named_call(if matches!(f, Eq) { "rvec_eq" } else { "rvec_ne" }, vec![a(0), a(1)]))
            }
            Eq if same_operands(self) && !self.fe.holds_unfaithful_eq(self.ty_adj(arg_exprs[0]).peel_refs(), &mut HashSet::new()) => {
                Some(Self::mk_bin("==", 44, &a(0), &a(1)))
            }
            Ne if same_operands(self) && !self.fe.holds_unfaithful_eq(self.ty_adj(arg_exprs[0]).peel_refs(), &mut HashSet::new()) => {
                Some(Self::mk_bin("!=", 44, &a(0), &a(1)))
            }
            // AutoCorrode's `cmp` needs an `order` on the operands' HOL type
            Cmp if !target.is_local() && self.hol_ordered(self.ty_adj(arg_exprs[0]).peel_refs()) => {
                Some(self.named_call("cmp", vec![a(0), a(1)]))
            }
            // strings by their bytes
            Cmp if !target.is_local() && self.str_like(self.ty_adj(arg_exprs[0]).peel_refs()) => {
                Some(self.named_call("str_cmp", vec![a(0), a(1)]))
            }
            OptionUnwrap => Some(self.named_call("option_unwrap", vec![a(0)])),
            // the message is a Rust string, the panic message a HOL `String.literal`
            OptionExpect => Some(self.named_call("option_expect_str", vec![a(0), a(1)])),
            OptionIsSome => Some(self.named_call("urust_func_option_is_some", vec![a(0)])),
            OptionIsNone => Some(self.named_call("urust_func_option_is_none", vec![a(0)])),
            OptionOkOr => Some(self.named_call("ok_or", vec![a(0), a(1)])),
            OptionTake => Some(self.named_call("take_mut_ref_option", vec![a(0)])),
            ResultUnwrap => Some(self.named_call("result_unwrap", vec![a(0)])),
            ResultExpect => Some(self.named_call("result_expect_str", vec![a(0), a(1)])),
            ResultIsOk => Some(self.named_call("urust_func_result_is_ok", vec![a(0)])),
            ResultIsErr => Some(self.named_call("urust_func_result_is_err", vec![a(0)])),
            ResultOk => Some(self.named_call("ok", vec![a(0)])),
            ResultUnwrapOr => Some(self.named_call("result_unwrap_or", vec![a(0), a(1)])),
            Len => Some(self.named_call("len", vec![a(0)])),
            VecNew | VecWithCapacity => {
                let t = self.ty_of(e);
                let mut args = vec![self.vec_layout(t)];
                let model = if matches!(f, VecNew) { "rvec_new" } else {
                    args.push(a(0));
                    "rvec_with_capacity"
                };
                let call = self.named_call(model, args);
                let h = self.hty(t);
                Some(self.typed("vec", call, &h))
            }
            StringNew => Some(Tr::atom("[]")),
            VecFromList | VecAlloc | FromUtf8ErrorIntoBytes => {
                let l = self.vec_layout(self.ty_of(e));
                Some(match f {
                    VecFromList => self.named_call("rvec_from_list", vec![l, a(0)]),
                    VecAlloc => self.named_call("rvec_of_list_alloc", vec![l, a(0)]),
                    _ => {
                        let bytes = self.named_call("from_utf8_error_into_bytes", vec![a(0)]);
                        self.named_call("rvec_of_list_alloc", vec![l, bytes])
                    }
                })
            }
            VecElems => Some(self.to_val(self.vec_elems(PV::Val(a(0))))),
            StringFromUtf8 => {
                let bytes = self.to_val(self.vec_elems(PV::Val(a(0))));
                Some(self.named_call("string_from_utf8", vec![bytes]))
            }
            BoxNew => Some(a(0)),
            // the destructor, if any
            Drop => {
                let t = self.ty_adj(arg_exprs[0]);
                let tmp = self.fresh("dropped");
                let g = self.drop_glue(t, PV::Val(Tr::atom(tmp.clone())))?;
                Some(Tr::block(format!("{{ let {} = {}; {} () }}", tmp, a(0).s, g.join("\n"))))
            }
            RangeInclusiveNew => Some(Tr::new(format!("{} ..= {}", a(0).at(42), a(1).at(42)), 41)),
            // between a `Vec` and the list of its elements (`IntoIterator::into_iter`, `From`, ...):
            // the elements; a new `Vec` of the elements of an array by value (`From<[T; N]>`, a
            // boxed slice) or of a copy of a list (`From<&[T]>`, `to_owned`); `to_owned` of a `Vec`
            // is its clone
            Conversion if !arg_exprs.is_empty() && let Some(c) = self.vec_conversion(self.ty_adj(arg_exprs[0]), self.ty_of(e), target) => {
                let x = a(0);
                Some(match c {
                    VecConversion::Elems => self.to_val(self.vec_elems(PV::Val(x))),
                    VecConversion::FromList(l) => self.named_call("rvec_from_list", vec![l, x]),
                    VecConversion::Alloc(l) => self.named_call("rvec_of_list_alloc", vec![l, x]),
                    VecConversion::Clone => self.named_call("rvec_clone", vec![x]),
                })
            }
            Conversion | SliceIter | ToString if same_hol(self) => Some(a(0)),
            // the `Display` text of a value of a type with a model of `Display` (see `fmt_model`),
            // with the default options; a character's is its encoding
            ToString => {
                let src = self.ty_adj(arg_exprs[0]).peel_refs();
                if src.is_char() {
                    Some(self.named_call("char_to_string", vec![a(0)]))
                } else {
                    self.fmt_model("Display", src).map(|n| {
                        let text = Tr::atom(format!("\\<llangle>{}_text\\<rrangle>", n));
                        self.named_call("fmt_to_string", vec![text, Tr::atom(format!("{}_u32", FMT_DEFAULT_FLAGS)), a(0)])
                    })
                }
            }
            // a lossless conversion between integers and characters (`From`, `Into`): the value, as
            // `as` converts it (a `char` is its code point, a `u32`); a character to a `String`
            // (`From`, `ToString`): its encoding
            Conversion if !arg_exprs.is_empty() => {
                let src = self.ty_adj(arg_exprs[0]).peel_refs();
                let dst = self.ty_of(e);
                match Self::int_or_char_suffix(dst) {
                    Some(sfx) if src.is_bool() => Some(Tr::new(format!("if {} {{ 1_{} }} else {{ 0_{} }}", a(0).at(20), sfx, sfx), 21)),
                    Some(sfx) if Self::int_or_char_suffix(src).is_some() => Some(Tr::new(format!("({}) as {}", a(0).s, sfx), 299)),
                    // `String::from(c)`
                    None if src.is_char() && self.str_like(dst) => Some(self.named_call("char_to_string", vec![a(0)])),
                    _ => None,
                }
            }
            IntOp(op) => Some(self.named_call(op, vec![a(0), a(1)])),
            Model(n) => Some(self.named_call(n, argv.to_vec())),
            // the HOL type of the result is not determined by the arguments'
            ModelTyped(n) => {
                let call = self.named_call(n, argv.to_vec());
                let h = self.hty(self.ty_of(e));
                Some(self.typed("res", call, &h))
            }
            // `get` by an index, or by a range (whose HOL value is a `range` or its only field)
            SliceGet => {
                let it = self.ty_adj(arg_exprs[1]).peel_refs();
                let m = match it.kind() {
                    ty::Uint(ty::UintTy::Usize) => Some("slice_get"),
                    ty::Adt(d, _) => match self.fe.std_adt(d.did()) {
                        Some("Range" | "RangeInclusive") => Some("slice_get_range"),
                        Some("RangeTo") => Some("slice_get_to"),
                        Some("RangeToInclusive") => Some("slice_get_to_inclusive"),
                        Some("RangeFrom") => Some("slice_get_from"),
                        Some("RangeFull") => Some("slice_get_full"),
                        _ => None,
                    },
                    _ => None,
                };
                m.map(|m| self.named_call(m, vec![a(0), a(1)]))
            }
            SliceGetMut if self.ty_adj(arg_exprs[1]).peel_refs().is_usize() => Some(self.named_call("slice_get_mut", vec![a(0), a(1)])),
            SliceGetMut if matches!(self.range_kind(self.ty_adj(arg_exprs[1]).peel_refs()), Some(RangeKind::Range | RangeKind::Inclusive)) => {
                Some(self.named_call("slice_get_range_mut", vec![a(0), a(1)]))
            }
            // `iter_mut()` as a value (in a `for` loop, see `for_loop`)
            SliceIterMut => Some(self.named_call("slice_iter_mut_list", vec![a(0)])),
            // of an integer range (AutoCorrode's `contains`)
            RangeContains => match self.ty_adj(arg_exprs[0]).peel_refs().kind() {
                ty::Adt(_, ra) if ra.type_at(0).is_integral() && ra.type_at(0) == self.ty_adj(arg_exprs[1]).peel_refs() => {
                    Some(self.named_call("contains", vec![a(0), a(1)]))
                }
                _ => None,
            },
            SliceCopyWithin => match self.ty_adj(arg_exprs[1]).peel_refs().kind() {
                ty::Adt(d, _) if matches!(self.fe.std_adt(d.did()), Some("Range" | "RangeInclusive")) => {
                    Some(self.named_call("slice_copy_within", vec![a(0), a(1), a(2)]))
                }
                _ => None,
            },
            // `TryInto::try_into` / `TryFrom::try_from` from a slice to an array of length `N` (or
            // to a reference to one): `Ok` iff the slice has `N` elements
            TryIntoArray => {
                let ty::Adt(_, rargs) = self.ty_of(e).kind() else { return Ok(None) };
                // the array, or a reference to it, or (from a `Vec`) a `Box` of it
                // (normalised: an array length given by a constant item is evaluated)
                let env = self.typing_env();
                // not to `&mut [T; N]`, which aliases the slice (a copy would lose the writes)
                let target = rargs.types().next().filter(|t| !matches!(t.kind(), ty::Ref(_, _, m) if m.is_mut()));
                let target = target.map(|t| t.peel_refs()).map(|t| match t.kind() {
                    ty::Adt(d, a) if d.is_box() => a.type_at(0),
                    _ => t,
                });
                let target = target.map(|t| crate::frontend::try_normalize(self.tcx, env, ty::Unnormalized::new_wip(t)).unwrap_or(t));
                let src = self.ty_adj(arg_exprs[0]);
                let model = match src.kind() {
                    // from `&[T]` (the value of a `&mut [T]` is a reference, not the list)
                    ty::Ref(_, s, m) if !m.is_mut() && s.is_slice() => Some("slice_try_into_array"),
                    // `TryFrom<Vec<T>>`, `TryFrom<Box<[T]>>` (by value): the error is the argument
                    ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("Vec") => Some("rvec_try_into_array"),
                    ty::Adt(d, a) if d.is_box() && a.type_at(0).is_slice() => Some("vec_try_into_array"),
                    _ => None,
                };
                match (model, target.map(|t| *t.kind())) {
                    (Some(m), Some(ty::Array(_, n))) => {
                        n.try_to_target_usize(self.tcx).map(|n| self.named_call(m, vec![a(0), Tr::atom(format!("{}_usize", n))]))
                    }
                    _ => None,
                }
            }
            // a `char` or a string pattern (a closure or a slice of characters has no model)
            StrPattern(base) => {
                let pt = self.ty_adj(arg_exprs[1]).peel_refs();
                if pt.is_char() {
                    Some(self.named_call(&format!("{}_char", base), vec![a(0), a(1)]))
                } else if self.str_like(pt) {
                    Some(self.named_call(&format!("{}_str", base), vec![a(0), a(1)]))
                } else {
                    None
                }
            }
            AsciiTest(p) => Some(self.named_call("ascii_test", vec![Tr::atom(format!("\\<llangle>{}\\<rrangle>", p)), a(0)])),
            // `str::get` by a range
            StrGet => {
                let m = match self.range_kind(self.ty_adj(arg_exprs[1]).peel_refs()) {
                    Some(RangeKind::Range | RangeKind::Inclusive) => Some("str_get_range"),
                    Some(RangeKind::To) => Some("str_get_to"),
                    Some(RangeKind::ToInclusive) => Some("str_get_to_inclusive"),
                    Some(RangeKind::From) => Some("str_get_from"),
                    Some(RangeKind::Full) => return Ok(Some(Tr::new(format!("Some({})", a(0).s), 999))),
                    None => None,
                };
                m.map(|m| self.named_call(m, vec![a(0), a(1)]))
            }
            // `String + &str`: the concatenation; `String += &str`: appends
            StringAdd if self.str_like(self.ty_adj(arg_exprs[0]).peel_refs()) => Some(self.named_call("string_add", vec![a(0), a(1)])),
            StringAddAssign if self.str_like(self.ty_adj(arg_exprs[0]).peel_refs()) => {
                Some(self.named_call("vec_extend_from_slice", vec![a(0), a(1)]))
            }
            // `str::parse::<F>` for an integer type `F` (the result's type is stated by `result_stated`)
            StrParse => match gargs.types().next().map(|t| t.kind()) {
                Some(ty::Uint(_)) => Some(self.named_call("str_parse_word", vec![a(0)])),
                Some(ty::Int(_)) => Some(self.named_call("str_parse_sword", vec![a(0)])),
                _ => None,
            },
            OrdMin | OrdMax if matches!(self.ty_adj(arg_exprs[0]).peel_refs().kind(), ty::Uint(_)) => {
                Some(self.named_call(if f == OrdMin { "ord_min" } else { "ord_max" }, vec![a(0), a(1)]))
            }
            // `size_of::<T>()` at a type without parameters: its size in bytes, from its layout
            SizeOf => match gargs.types().next().filter(|t| !t.has_param()) {
                Some(t) => {
                    let env = ty::TypingEnv::fully_monomorphized();
                    self.tcx.layout_of(env.as_query_input(t)).ok().map(|l| Tr::atom(format!("{}_usize", l.size.bytes())))
                }
                None => None,
            },
            Iter(k) => self.iter_call(k, argv, arg_exprs, e),
            // the key `K`: the first type argument of `HashMap<K, V, S>`; a borrowed key `&Q` must
            // have its HOL type
            HashMapKey(n) => {
                let k = gargs.types().next().filter(|k| !k.has_param() && self.structural_eq_ty(*k, &mut HashSet::new()));
                let key_arg_ok = |this: &mut Self, k: Ty<'tcx>| {
                    arg_exprs.get(1).is_none_or(|x| this.fe.ty(this.ty_adj(x).peel_refs()) == this.fe.ty(k))
                };
                match k {
                    Some(k) if key_arg_ok(self, k) => Some(self.named_call(n, argv.to_vec())),
                    _ => None,
                }
            }
            SliceSort => match self.ty_adj(arg_exprs[0]).peel_refs().kind() {
                ty::Slice(t) => {
                    let c = self.ord_cmp_term(*t, &mut vec![]);
                    c.map(|c| self.named_call("slice_sort_by", vec![Tr::atom(format!("\\<llangle>{}\\<rrangle>", c)), a(0)]))
                }
                _ => None,
            },
            VecDedup => match self.ty_adj(arg_exprs[0]).peel_refs().kind() {
                ty::Adt(_, va) if self.structural_eq_ty(va.type_at(0), &mut HashSet::new()) => Some(self.named_call("rvec_dedup", vec![a(0)])),
                _ => None,
            },
            // a local enum translated to a `datatype` (one with fields): each variant's discriminant
            DiscriminantValue => match self.ty_adj(arg_exprs[0]).peel_refs().kind() {
                ty::Adt(def, _) if def.is_enum() && def.did().is_local() && def.variants().iter().any(|v| !v.fields.is_empty()) => {
                    let rt = self.ty_of(e);
                    let mut arms = vec![];
                    for (vidx, d) in def.discriminants(self.tcx) {
                        let env = self.typing_env();
                        let bits = self.tcx.layout_of(env.as_query_input(d.ty)).expect("a discriminant type has a layout").size.bits();
                        // a negative discriminant (its sign bit set) is not handled
                        if d.ty.is_signed() && (d.val >> (bits - 1)) & 1 == 1 { return Ok(None) }
                        let n = def.variant(vidx).fields.len();
                        let pat = self.ctor_pat(def.did(), vidx.as_usize(), vec!["_".to_string(); n])?;
                        arms.push(format!("{} \\<Rightarrow> {}", pat, Self::int_lit(d.val, false, rt)?.s));
                    }
                    Some(Tr::block(format!("match {} {{\n{}\n}}", a(0).at(20), arms.join(",\n"))))
                }
                _ => None,
            },
            PartialCmp => {
                let l = self.ty_adj(arg_exprs[0]).peel_refs();
                let r = self.ty_adj(arg_exprs[1]).peel_refs();
                (matches!(l.kind(), ty::Uint(_)) && l == r).then(|| self.named_call("partial_cmp_word", vec![a(0), a(1)]))
            }
            DefaultFn if argv.is_empty() => self.default_value(self.ty_of(e), &mut vec![])?,
            // the models of AutoCorrode's `StdLib_Frontend_Models`
            SliceSwap => Some(self.named_call("slice_swap", vec![a(0), a(1), a(2)])),
            VecFromElem => {
                let l = self.vec_layout(self.ty_of(e));
                Some(self.named_call("rvec_from_elem", vec![l, a(0), a(1)]))
            }
            // a method of `Formatter` (or of `fmt::Write` on a `Formatter`)
            FmtMethod(n) if self.is_formatter(self.ty_adj(arg_exprs[0])) => Some(self.named_call(n, argv.to_vec())),
            // a formatting trait's `fmt` on a primitive type
            FmtTrait(tr) => {
                let label = self.fmt_trait(tr).map(str::to_string);
                label.and_then(|l| self.fmt_model(&l, self.ty_adj(arg_exprs[0]).peel_refs())).map(|n| self.named_call(&n, vec![a(0), a(1)]))
            }
            _ => None,
        };
        Ok(r)
    }

    /// Whether `PartialEq` on `t` is structural (HOL's equality): on the primitive types, `str`,
    /// `String`, and the tuples, arrays, slices and `Option`s of such types, and on local
    /// ADTs whose `PartialEq` is derived, with such fields. `seen`: the ADTs checked or being
    /// checked, each once (otherwise exponential in mutually recursive ADTs sharing fields, see
    /// `glue_in`). One in `seen` counts as structural: every case is a conjunction of its parts,
    /// so a part found not structural makes the whole answer false, and the ones in `seen` are
    /// structural or still being checked (a cycle, structural if the rest is).
    fn structural_eq_ty(&self, t: Ty<'tcx>, seen: &mut HashSet<Ty<'tcx>>) -> bool {
        match t.kind() {
            ty::Uint(_) | ty::Int(_) | ty::Bool | ty::Char | ty::Str => true,
            // not `&mut T`: its HOL value is a reference, whose equality is the address's
            ty::Ref(_, x, m) if !m.is_mut() => self.structural_eq_ty(*x, seen),
            ty::Slice(x) | ty::Array(x, _) => self.structural_eq_ty(*x, seen),
            ty::Tuple(ts) => ts.iter().all(|x| self.structural_eq_ty(x, seen)),
            ty::Adt(d, args) => match self.fe.std_adt(d.did()) {
                Some("String") => true,
                // not `Vec`: HOL's equality also compares the capacities
                Some("Option") => self.structural_eq_ty(args.type_at(0), seen),
                Some(_) => false,
                None if d.did().is_local() => {
                    if seen.contains(&t) { return true }
                    let Some(eq) = self.tcx.lang_items().eq_trait() else { return false };
                    let first_fn = self.tcx.associated_items(eq).in_definition_order().find(|i| i.is_fn()).map(|i| i.def_id);
                    let Some(m) = first_fn else { return false };
                    let derived = matches!(
                        self.resolve_instance(m, self.tcx.mk_args(&[t.into(), t.into()])),
                        Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), .. })) if self.derived(rd)
                    );
                    seen.insert(t);
                    derived && d.all_fields().all(|f| self.structural_eq_ty(f.ty(self.tcx, args).skip_normalization(), seen))
                }
                None => false,
            },
            _ => false,
        }
    }

    /// The HOL comparison (`'a => 'a => ordering`) of `Ord::cmp` on `t`: on unsigned and signed
    /// integers, `bool` and `char` by their values, and on local structs whose `Ord` is derived,
    /// lexicographically by their fields (with such comparisons).
    fn ord_cmp_term(&mut self, t: Ty<'tcx>, seen: &mut Vec<DefId>) -> Option<String> {
        match t.kind() {
            ty::Uint(_) | ty::Bool => Some("ord_cmp".into()),
            ty::Int(_) => Some("(\\<lambda>a b. ord_cmp (sint a) (sint b))".into()),
            // a `char` by its code point
            ty::Char => Some("ord_cmp".into()),
            // strings by their bytes (see `str_ord`)
            _ if self.str_like(t) => Some("str_ord".into()),
            // `Ord` on `&T` is `T`'s, and the HOL value of `&T` is that of `T`
            ty::Ref(_, x, m) if !m.is_mut() => self.ord_cmp_term(*x, seen),
            ty::Adt(d, args) if d.is_struct() && d.did().is_local() && self.fe.record_adts.contains(&d.did()) && !seen.contains(&d.did()) => {
                // `sort` compares with `PartialOrd::lt`: `Ord` and `PartialOrd` are derived, and
                // `lt` is derived or `PartialOrd`'s default (through the derived `partial_cmp`)
                let ord = self.tcx.get_diagnostic_item(sym::Ord)?;
                let cmp = self.tcx.associated_items(ord).filter_by_name_unhygienic(sym::cmp).next()?.def_id;
                let lt = self.tcx.get_diagnostic_item(Symbol::intern("cmp_partialord_lt"))?;
                let partial_cmp = self.tcx.get_diagnostic_item(Symbol::intern("cmp_partialord_cmp"))?;
                let resolves = |m: DefId, args: GenericArgsRef<'tcx>, default_ok: bool| {
                    matches!(self.resolve_instance(m, args), Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), .. }))
                        if self.derived(rd) || (default_ok && rd == m))
                };
                let one = self.tcx.mk_args(&[t.into()]);
                let two = self.tcx.mk_args(&[t.into(), t.into()]);
                if !(resolves(cmp, one, false) && resolves(partial_cmp, two, false) && resolves(lt, two, true)) {
                    return None;
                }
                seen.push(d.did());
                let mut parts = vec![];
                for (i, f) in d.all_fields().enumerate() {
                    let c = self.ord_cmp_term(f.ty(self.tcx, args).skip_normalization(), seen)?;
                    let sel = self.fe.field_name(d.did(), 0, i);
                    parts.push(format!("({} ({} a) ({} b))", c, sel, sel));
                }
                seen.pop();
                let body = parts.iter().rev().fold(None, |acc: Option<String>, p| {
                    Some(match acc {
                        None => p.clone(),
                        Some(r) => format!("(ordering_then {} {})", p, r),
                    })
                });
                Some(format!("(\\<lambda>a b. {})", body.unwrap_or_else(|| "Equal".into())))
            }
            _ => None,
        }
    }

    /// `Default::default()` of `t`: of the integer types, `bool`, `char`, `Option`, `Vec`, `String`,
    /// tuples and arrays of such types, and of local structs whose `Default` is derived (the
    /// defaults of their fields).
    fn default_value(&mut self, t: Ty<'tcx>, seen: &mut Vec<DefId>) -> R<Option<Tr>> {
        Ok(Some(match t.kind() {
            ty::Uint(_) | ty::Int(_) => Self::int_lit(0, false, t)?,
            ty::Bool => Tr::atom("false"),
            ty::Char => Tr::atom(format!("\\<llangle>{}\\<rrangle>", hol_char('\0'))),
            ty::Tuple(ts) if ts.is_empty() => Tr::atom("()"),
            ty::Tuple(ts) if ts.len() >= 2 => {
                let mut vs = vec![];
                for x in ts.iter() {
                    let Some(v) = self.default_value(x, seen)? else { return Ok(None) };
                    vs.push(v.at(11));
                }
                Tr::atom(format!("({})", vs.join(", ")))
            }
            ty::Array(x, n) => {
                let Some(n) = n.try_to_target_usize(self.tcx) else { return Ok(None) };
                let Some(v) = self.default_value(*x, seen)? else { return Ok(None) };
                let n = Self::int_lit(n as u128, false, self.tcx.types.usize)?;
                self.named_call("vec_from_elem", vec![v, n])
            }
            ty::Adt(d, args) => match self.fe.std_adt(d.did()) {
                Some("Option") => {
                    let h = self.hty(t);
                    self.typed("dflt", Tr::atom("None"), &h)
                }
                Some("Vec") => {
                    let l = self.vec_layout(t);
                    let call = self.named_call("rvec_new", vec![l]);
                    let h = self.hty(t);
                    self.typed("dflt", call, &h)
                }
                Some("String") => Tr::atom(format!("\\<llangle>{}\\<rrangle>", hol_str(""))),
                None if d.is_struct() && d.did().is_local() && !seen.contains(&d.did()) => {
                    let Some(dflt) = self.tcx.get_diagnostic_item(Symbol::intern("default_fn")) else { return Ok(None) };
                    let derived = matches!(
                        self.resolve_instance(dflt, self.tcx.mk_args(&[t.into()])),
                        Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), .. })) if self.derived(rd)
                    );
                    if !derived { return Ok(None) }
                    seen.push(d.did());
                    let mut vs = vec![];
                    for f in d.all_fields() {
                        let Some(v) = self.default_value(f.ty(self.tcx, args).skip_normalization(), seen)? else { return Ok(None) };
                        vs.push(v);
                    }
                    seen.pop();
                    self.ctor_call(d.did(), 0, vs)?
                }
                _ => return Ok(None),
            },
            _ => return Ok(None),
        }))
    }

    /// A method of `Iterator` (see `std_fn`) called on an iterator with a model (see
    /// `Frontend::iter_step`). An adapter's state is its fields, the inner iterator's state first
    /// (see `Frontend::ty`); the methods that run the iterator to its end take the crate's fuel.
    fn iter_call(&mut self, k: IterFn, argv: &[Tr], arg_exprs: &[&'tcx hir::Expr<'tcx>], e: &'tcx hir::Expr<'tcx>) -> Option<Tr> {
        let a = |i: usize| -> Tr { argv[i].clone() };
        let recv = self.ty_adj(arg_exprs[0]);
        let res = self.ty_of(e);
        let modelled = |this: &Self, t: Ty<'tcx>| matches!(t.kind(), ty::Adt(d, _) if this.fe.std_adt(d.did()).is_some());
        let tuple = |xs: Vec<String>| Tr::atom(format!("({})", xs.join(", ")));
        let step = |this: &Self, t: Ty<'tcx>| this.fe.iter_step(t, false).map(|s| Tr::atom(format!("\\<llangle>{}\\<rrangle>", s)));
        let fuel = Tr::atom("\\<llangle>urust_fuel\\<rrangle>".to_string());
        use IterFn::*;
        match k {
            // `next(&mut self)`, `any(&mut self, f)`: on the iterator itself (not through a further
            // reference)
            Next => match recv.kind() {
                ty::Ref(_, it, m) if m.is_mut() => step(self, *it).map(|s| self.named_call("iter_ref_next", vec![s, a(0)])),
                _ => None,
            },
            Any => match recv.kind() {
                ty::Ref(_, it, m) if m.is_mut() => step(self, *it).map(|s| self.named_call("iter_ref_any", vec![fuel, s, a(1), a(0)])),
                _ => None,
            },
            // the adapters take the iterator by value
            _ if !modelled(self, recv) => None,
            Enumerate if modelled(self, res) => Some(tuple(vec![a(0).s, "0_usize".into()])),
            // `zip(other)`: `other` is `IntoIterator::into_iter`'d, the identity when its HOL type is
            // that of the resulting iterator (an iterator, or a reference to a sequence), the
            // elements of a `Vec` whose list is that iterator's state (`vec::IntoIter`, `slice::Iter`)
            Zip => {
                let ty::Adt(_, zargs) = res.kind() else { return None };
                let b = zargs.types().nth(1)?;
                let other = self.ty_adj(arg_exprs[1]);
                if !modelled(self, res) { return None }
                let o = match other.peel_refs().kind() {
                    ty::Adt(_, va) if self.is_vec(other.peel_refs()) && self.fe.ty(Ty::new_slice(self.tcx, va.type_at(0))) == self.fe.ty(b) => {
                        self.to_val(self.vec_elems(PV::Val(a(1))))
                    }
                    _ if self.fe.ty(other.peel_refs()) == self.fe.ty(b) => a(1),
                    _ => return None,
                };
                Some(tuple(vec![a(0).s, o.s]))
            }
            Skip | Take | Map | Filter if modelled(self, res) => Some(tuple(vec![a(0).s, a(1).s])),
            TakeWhile if modelled(self, res) => Some(tuple(vec![a(0).s, "False".into(), a(1).s])),
            Same if modelled(self, res) => Some(a(0)),
            Count => step(self, recv).map(|s| self.named_call("iter_count", vec![fuel.clone(), s, a(0)])),
            ForEach => step(self, recv).map(|s| self.named_call("iter_for_each", vec![fuel.clone(), s, a(1), a(0)])),
            // the least of unsigned integers
            Min => match res.kind() {
                ty::Adt(_, oa) if matches!(oa.types().next().map(|t| *t.kind()), Some(ty::Uint(_))) => {
                    step(self, recv).map(|s| self.named_call("iter_min", vec![fuel.clone(), s, a(0)]))
                }
                _ => None,
            },
            Collect => match res.kind() {
                ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("Vec") => {
                    let l = self.vec_layout(res);
                    step(self, recv).map(|s| {
                        let xs = self.named_call("iter_collect_list", vec![fuel, s, a(0)]);
                        self.named_call("rvec_of_list_alloc", vec![l, xs])
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Is `did` a function `fn<T>(T) -> T` whose type parameter has no bound with methods? Its
    /// only total implementation returns its argument.
    fn identity_shaped(&self, did: DefId) -> bool {
        let tcx = self.tcx;
        let sig = tcx.fn_sig(did).instantiate_identity().skip_binder();
        let [i] = sig.inputs() else { return false };
        matches!(i.kind(), ty::Param(_))
            && sig.output() == *i
            && tcx.generics_of(did).own_counts().types == 1
            && tcx.param_env(did).caller_bounds().all(|c| {
                c.as_trait_clause().is_none_or(|t| tcx.associated_items(t.def_id()).in_definition_order().next().is_none())
            })
    }

    /// Does AutoCorrode's `cmp` apply to the HOL type of `t` (see `Frontend::ty`)? It is defined
    /// on words only, comparing them as signed words for the signed integer types.
    fn hol_ordered(&self, t: Ty<'tcx>) -> bool {
        match t.kind() {
            ty::Uint(_) | ty::Int(_) | ty::Char => true,
            _ => false,
        }
    }

    /// A conversion by `f` from `src` to `dst` (see `StdFn::Conversion`) between a `Vec` and the
    /// list of its elements, or `to_owned` of a `Vec`.
    fn vec_conversion(&mut self, src: Ty<'tcx>, dst: Ty<'tcx>, f: DefId) -> Option<VecConversion> {
        let (s, d) = (src.peel_refs(), dst.peel_refs());
        let elems_of = |this: &mut Self, v: Ty<'tcx>, l: Ty<'tcx>| match v.kind() {
            ty::Adt(_, args) => this.fe.ty(Ty::new_slice(this.tcx, args.type_at(0))) == this.fe.ty(l),
            _ => false,
        };
        match (self.is_vec(s), self.is_vec(d)) {
            (true, true) if self.tcx.is_diagnostic_item(Symbol::intern("to_owned_method"), f) => Some(VecConversion::Clone),
            (true, false) if elems_of(self, s, d) => Some(VecConversion::Elems),
            (false, true) if elems_of(self, d, s) => {
                let l = self.vec_layout(d);
                // an array by value (a `Box` of one is the same HOL value)
                let by_value = matches!(src.kind(), ty::Array(..)) || matches!(src.kind(), ty::Adt(b, a) if b.is_box() && matches!(a.type_at(0).kind(), ty::Array(..) | ty::Slice(_)));
                Some(if by_value { VecConversion::FromList(l) } else { VecConversion::Alloc(l) })
            }
            _ => None,
        }
    }

    /// `a == b` on the type `t` (behind references) whose derived `PartialEq` is translated (see
    /// `Frontend::translated_derived`): the call of its `eq`; `None` for other types.
    fn translated_eq(&mut self, t: Ty<'tcx>, a: Tr, b: Tr) -> R<Option<Tr>> {
        let tcx = self.tcx;
        let t = t.peel_refs();
        let eq_trait = tcx.lang_items().eq_trait().expect("`PartialEq` is a lang item");
        let eq = tcx
            .associated_items(eq_trait)
            .in_definition_order()
            .find(|i| i.is_fn() && i.name() == sym::eq)
            .expect("`PartialEq` has `eq`")
            .def_id;
        match self.resolve_instance(eq, tcx.mk_args(&[t.into(), t.into()])) {
            Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), args })) if self.fe.translated_derived(rd) => {
                Ok(Some(self.local_call(rd, args, vec![a, b])?))
            }
            _ => Ok(None),
        }
    }

    /// A `Vec` whose elements are compared by HOL's equality (they hold no `HashMap` or `Vec`):
    /// its `PartialEq` is AutoCorrode's `rvec_eq`.
    fn vec_of_hol_eq(&self, t: Ty<'tcx>) -> bool {
        match t.kind() {
            ty::Adt(_, args) if self.is_vec(t) => !self.fe.holds_unfaithful_eq(args.type_at(0), &mut HashSet::new()),
            _ => false,
        }
    }

    /// A method of a derived implementation that is modelled (not translated, see
    /// `Frontend::translated_derived`).
    fn derived(&self, did: DefId) -> bool {
        self.tcx.impl_of_assoc(did).map(|i| self.tcx.is_automatically_derived(i)).unwrap_or(false) && !self.fe.translated_derived(did)
    }

    /// Is `e` built only from locals and constants, literals, field accesses, indexing and
    /// built-in operators? Such an expression has no side effects, so evaluating it again or
    /// in another order gives the same result.
    fn is_simple(&self, e: &hir::Expr<'tcx>) -> bool {
        let builtin = self.typeck.type_dependent_def_id(e.hir_id).is_none();
        match e.kind {
            ExprKind::Path(_) | ExprKind::Lit(_) => true,
            ExprKind::Field(b, _) | ExprKind::DropTemps(b) => self.is_simple(b),
            ExprKind::Unary(_, b) => builtin && self.is_simple(b),
            ExprKind::Index(b, i, _) => self.is_simple(b) && self.is_simple(i),
            ExprKind::Binary(_, l, r) => builtin && self.is_simple(l) && self.is_simple(r),
            _ => false,
        }
    }

    // ------------------------------------------------------------------
    // Structs
    // ------------------------------------------------------------------

    fn struct_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        qp: &'tcx hir::QPath<'tcx>,
        fields: &'tcx [hir::ExprField<'tcx>],
        tail: hir::StructTailExpr<'tcx>,
    ) -> R<Tr> {
        let t = self.ty_of(e);
        let ty::Adt(def, _) = t.kind() else { return unsup("struct expression of non-ADT type") };
        let adt = def.did();
        if let Some(k) = self.fe.std_adt(adt) {
            if k == "Range" && fields.len() == 2 {
                let mut st = None;
                let mut en = None;
                for f in fields {
                    let v = self.val(f.expr)?;
                    // the fields `a..b` is lowered to (`Range { start: a, end: b }`)
                    if f.ident.name == sym::start { st = Some(v) } else { en = Some(v) }
                }
                let (Some(a), Some(b)) = (st, en) else { return unsup("range") };
                return Ok(Tr::new(format!("{} .. {}", a.at(42), b.at(42)), 41));
            }
            // `a..`, `..b`, `..=b`: their only field (see `Frontend::ty`)
            if matches!(k, "RangeFrom" | "RangeTo" | "RangeToInclusive") && let [f] = fields {
                return self.val(f.expr);
            }
            if k == "RangeFull" && fields.is_empty() {
                return Ok(Tr::atom("()"));
            }
            return unsup(format!("struct expression of `{}`", t));
        }
        if !adt.is_local() || def.is_union() { return unsup(format!("struct expression of `{}`", t)) }
        self.opaque_adt(adt)?;
        let variant = def.variant_of_res(self.typeck.qpath_res(qp, e.hir_id));
        let vidx = def.variant_index_with_id(variant.def_id).as_usize();
        let nf = variant.fields.len();
        let mut vals: Vec<Option<Tr>> = vec![None; nf];
        let mut pre = vec![];
        // Rust evaluates the written fields in source order, then the base; the uRust struct
        // expression lists the fields in declaration order. When that reorders evaluation and
        // an expression may have side effects, the written fields are first bound to temporaries.
        let base = match tail { hir::StructTailExpr::Base(b) => Some(b), _ => None };
        let idxs: Vec<usize> = fields.iter().map(|f| self.typeck.field_index(f.hir_id).as_usize()).collect();
        let reordered = base.is_some() || idxs.windows(2).any(|w| w[0] > w[1]);
        let effects = fields.iter().map(|f| f.expr).chain(base).any(|x| !self.is_simple(x));
        let need_tmp = reordered && effects;
        for (f, &idx) in fields.iter().zip(&idxs) {
            let v = self.val(f.expr)?;
            if need_tmp {
                let tmp = self.fresh("fld");
                pre.push(format!("let {} = {};", tmp, v.at(20)));
                vals[idx] = Some(Tr::atom(tmp));
            } else {
                vals[idx] = Some(v);
            }
        }
        match tail {
            hir::StructTailExpr::Base(b) => {
                let bv = self.val(b)?;
                let tmp = self.fresh("base");
                pre.push(format!("let {} = {};", tmp, bv.at(20)));
                for k in 0..nf {
                    if vals[k].is_none() {
                        vals[k] = Some(self.field_read(adt, k, &Tr::atom(tmp.clone()))?);
                    }
                }
            }
            hir::StructTailExpr::None => {}
            _ => return unsup("default field values in struct expression"),
        }
        // rustc requires every field to be given, or a base
        let vals: Vec<Tr> = vals.into_iter().map(|v| v.expect("every field has a value")).collect();
        let core = if nf == 0 {
            Tr::atom(self.fe.variant_ctor_name(adt, vidx))
        } else if def.is_enum() {
            self.ctor_call(adt, vidx, vals)?
        } else {
            if nf > 8 { return Ok(self.ctor_many(adt, vidx, vals, pre)) }
            let n = self.fe.variant_call_name(adt, vidx);
            let fs: Vec<String> = (0..nf).map(|k| {
                let fname = self.fe.field_name(adt, vidx, k);
                format!("{}: {}", fname, vals[k].at(11))
            }).collect();
            Tr::atom(format!("{} {{ {} }}", n, fs.join(", ")))
        };
        if pre.is_empty() { Ok(core) } else { Ok(Tr::block(format!("{{\n{}\n{}\n}}", pre.join("\n"), core.s))) }
    }

    // ------------------------------------------------------------------
    // Control flow
    // ------------------------------------------------------------------

    fn strip_drop_temps(e: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
        match e.kind { ExprKind::DropTemps(x) => Self::strip_drop_temps(x), _ => e }
    }

    fn branch(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<String> {
        match e.kind {
            ExprKind::Block(b, None) => self.block_seq(b.stmts, b.expr),
            _ => Ok(self.expr(e).s),
        }
    }

    fn if_expr(&mut self, c: &'tcx hir::Expr<'tcx>, t: &'tcx hir::Expr<'tcx>, el: Option<&'tcx hir::Expr<'tcx>>) -> R<Tr> {
        let c = Self::strip_drop_temps(c);
        if let ExprKind::Let(le) = c.kind {
            let iv = self.scrut(le.init)?;
            let place = self.scrut_place(le.init)?;
            let p = self.pat_at(le.pat, place)?;
            let tb = with_prologue(&p.prologue, &self.branch(t)?);
            let eb = match el { Some(x) => self.branch(x)?, None => "()".into() };
            // uRust's `if let`, like its `while let`, takes no pattern conditions and only
            // variables in a tuple pattern; otherwise `match e { p => t, _ => e }`
            let tuple = matches!(le.pat.kind, PatKind::Tuple(..)) || tuple_of_non_variables(le.pat);
            if p.conds.is_empty() && !tuple {
                return Ok(Tr::new(format!("if let {} = {} {{\n{}\n}} else {{\n{}\n}}", p.pat, iv.at(20), tb, eb), 11));
            }
            let guard = if p.conds.is_empty() { String::new() } else { format!(" if {}", p.conds.join(" && ")) };
            return Ok(Tr::new(format!(
                "match {} {{\n  {}{} \\<Rightarrow> {{\n{}\n}},\n  _ \\<Rightarrow> {{\n{}\n}}\n}}",
                iv.at(20), p.pat, guard, tb, eb
            ), 20));
        }
        if contains_let(c) { return unsup("`let` chain in `if` condition") }
        let cv = self.val(c)?;
        let tb = self.branch(t)?;
        match el {
            None => Ok(Tr::new(format!("if {} {{\n{}\n}}", cv.at(20), tb), 20)),
            Some(x) => {
                let eb = self.branch(x)?;
                Ok(Tr::new(format!("if {} {{\n{}\n}} else {{\n{}\n}}", cv.at(20), tb, eb), 21))
            }
        }
    }

    /// `e?` on a `Result` whose error type differs from the one returned: Rust converts the error
    /// with `From::from`, which uRust's `?` does not; the conversion is made explicit.
    fn try_error_conversion(&mut self, inner: &'tcx hir::Expr<'tcx>, arms: &'tcx [hir::Arm<'tcx>], v: &Tr, drops: &[String]) -> R<Option<Tr>> {
        // the `Break` arm of the desugaring returns the function's result type
        let Some(ret) = arms.iter().find_map(|a| match a.body.kind {
            ExprKind::Ret(Some(r)) => Some(r),
            _ => None,
        }) else {
            return Ok(None);
        };
        let from = self.ty_adj(inner).peel_refs();
        let to = self.ty_of(ret);
        let (ty::Adt(fd, fa), ty::Adt(td, ta)) = (from.kind(), to.kind()) else { return Ok(None) };
        // an early return with drops: `return { let r = <residual>; drops; r }`
        let ret_with = |s: &mut Self, r: String| -> String {
            if drops.is_empty() { return format!("return {};", r) }
            format!("return {{\n{}\n}};", s.then_drops(&r, drops))
        };
        if !drops.is_empty() && self.fe.std_adt(fd.did()) == Some("Option") && self.fe.std_adt(td.did()) == Some("Option") {
            let x = self.fresh("some");
            let none = ret_with(self, "None".to_string());
            return Ok(Some(Tr::new(
                format!("match {} {{\n  Some({}) \\<Rightarrow> {},\n  None \\<Rightarrow> {{ {} }}\n}}", v.at(20), x, x, none),
                20,
            )));
        }
        if self.fe.std_adt(fd.did()) != Some("Result") || self.fe.std_adt(td.did()) != Some("Result") {
            return Ok(None);
        }
        let (e1, e2) = (fa.type_at(1), ta.type_at(1));
        if e1 == e2 && drops.is_empty() {
            return Ok(None);
        }
        let Some(from_fn) = self.tcx.lang_items().get(LangItem::FromFn) else { return unsup("`?` with an error conversion") };
        let args = self.tcx.mk_args(&[e2.into(), e1.into()]);
        let err = self.fresh("err");
        let conv = if e1 == e2 { Tr::atom(err.clone()) } else { match self.resolve_instance(from_fn, args) {
            Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), args: rargs })) if self.fe.local_fn_with_body(rd) => {
                self.local_call(rd, rargs, vec![Tr::atom(err.clone())])?
            }
            Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), .. })) => {
                let n = self.fe.ext_fun(rd, false);
                let call = self.named_call(&n, vec![Tr::atom(err.clone())]);
                let h = self.hty(e2);
                self.typed("res", call, &h)
            }
            _ => return unsup("`?` with an unresolved error conversion"),
        } };
        let ok = self.fresh("ok");
        let back = ret_with(self, format!("Err({})", conv.at(11)));
        Ok(Some(Tr::new(
            format!("match {} {{\n  Ok({}) \\<Rightarrow> {},\n  Err({}) \\<Rightarrow> {{ {} }}\n}}", v.at(20), ok, ok, err, back),
            20,
        )))
    }

    fn loop_expr(&mut self, e: &'tcx hir::Expr<'tcx>, b: &'tcx hir::Block<'tcx>, label: Option<Label>, src: LoopSource) -> R<Tr> {
        self.drop_scopes.push(DropScope::Loop(e.hir_id));
        let r = self.loop_expr_scoped(e, b, label, src);
        self.drop_scopes.pop();
        r
    }

    fn loop_expr_scoped(&mut self, e: &'tcx hir::Expr<'tcx>, b: &'tcx hir::Block<'tcx>, label: Option<Label>, src: LoopSource) -> R<Tr> {
        let lbl = loop_label(label);
        let t = self.ty_of(e);
        // a `loop` producing a value: a mutable local holds it, set by the `break`s (it stays
        // `undefined` if the loop runs out of fuel, as `let x;` without a value)
        if !(t.is_unit() || t.is_never()) {
            if !matches!(src, LoopSource::Loop) { return unsup("loop producing a value (`break` with a value)") }
            let a = self.alloc(t)?;
            let res = self.fresh("lres");
            let h = self.hty(t);
            let init = self.let_binding(&res, hir::Mutability::Mut, &a, &format!("\\<llangle>undefined :: {}\\<rrangle>", h));
            self.loop_results.insert(e.hir_id, res.clone());
            let body = self.block_seq(b.stmts, b.expr);
            self.loop_results.remove(&e.hir_id);
            return Ok(Tr::block(format!("{{\n{}\n{} {}loop {{\n{}\n}};\n* {}\n}}", init, FUEL, lbl, body?, res)));
        }
        match src {
            LoopSource::While => {
                // loop { if cond { body } else { break } }
                let Some(ife) = b.expr else { return unsup("while desugaring") };
                let ExprKind::If(cond, then, _) = ife.kind else { return unsup("while desugaring") };
                let cond = Self::strip_drop_temps(cond);
                if let ExprKind::Let(le) = cond.kind {
                    let iv = self.scrut(le.init)?;
                    let place = self.scrut_place(le.init)?;
                    let p = self.pat_at(le.pat, place)?;
                    let body = with_prologue(&p.prologue, &self.branch(then)?);
                    let tuple = matches!(le.pat.kind, PatKind::Tuple(..)) || tuple_of_non_variables(le.pat);
                    if p.conds.is_empty() && !tuple {
                        return Ok(Tr::new(format!("{} {}while let {} = {} {{\n{}\n}}", FUEL, lbl, p.pat, iv.at(20), body), 11));
                    }
                    // uRust's `while let` takes no pattern conditions and only variables in a tuple
                    // pattern; otherwise Rust's own expansion: `loop { match e { p => body, _ => break } }`
                    let guard = if p.conds.is_empty() { String::new() } else { format!(" if {}", p.conds.join(" && ")) };
                    return Ok(Tr::new(
                        format!(
                            "{FUEL} {lbl}loop {{\nmatch {} {{\n  {}{} \\<Rightarrow> {{\n{}\n}},\n  _ \\<Rightarrow> {{ break; }}\n}};\n}}",
                            iv.at(20),
                            p.pat,
                            guard,
                            body
                        ),
                        11,
                    ));
                }
                if contains_let(cond) { return unsup("`let` chain in `while` condition") }
                let cv = self.val(cond)?;
                let body = self.branch(then)?;
                Ok(Tr::new(format!("{} {}while {} {{\n{}\n}}", FUEL, lbl, cv.at(20), body), 11))
            }
            LoopSource::Loop => {
                let body = self.block_seq(b.stmts, b.expr)?;
                Ok(Tr::new(format!("{} {}loop {{\n{}\n}}", FUEL, lbl, body), 11))
            }
            LoopSource::ForLoop => unsup("for-loop desugaring"),
        }
    }

    /// The receiver of `e` if it is a call (without further arguments) of the standard library
    /// function `f` (e.g. the slice method `iter`, also through `Vec` and arrays).
    fn std_method_recv(&self, e: &'tcx hir::Expr<'tcx>, f: StdFn) -> Option<&'tcx hir::Expr<'tcx>> {
        let ExprKind::MethodCall(_, recv, [], _) = e.kind else { return None };
        let did = self.typeck.type_dependent_def_id(e.hir_id)?;
        (self.std_fn(did) == Some(f)).then_some(recv)
    }

    fn for_loop(&mut self, head_call: &'tcx hir::Expr<'tcx>, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        // the loop of the desugaring is the target of the body's `break`s and `continue`s
        let target = arms.first().map(|a| a.body.hir_id);
        if let Some(t) = target {
            self.drop_scopes.push(DropScope::Loop(t));
        }
        let r = self.for_loop_scoped(head_call, arms);
        if target.is_some() {
            self.drop_scopes.pop();
        }
        r
    }

    fn for_loop_scoped(&mut self, head_call: &'tcx hir::Expr<'tcx>, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        // match IntoIterator::into_iter(<head>) { mut iter => loop { match next(&mut iter) { None => break, Some(<pat>) => <body> } } }
        let ExprKind::Call(_, [head]) = head_call.kind else { return unsup("for-loop head") };
        let [arm] = arms else { return unsup("for-loop desugaring") };
        let ExprKind::Loop(lb, label, LoopSource::ForLoop, _) = arm.body.kind else { return unsup("for-loop desugaring") };
        let lbl = loop_label(label);
        let stmt_exprs = lb.stmts.iter().filter_map(|s| match s.kind {
            StmtKind::Expr(x) | StmtKind::Semi(x) => Some(x),
            _ => None,
        });
        let inner_match = stmt_exprs.chain(lb.expr).find_map(|x| match x.kind {
            ExprKind::Match(next, arms2, MatchSource::ForLoopDesugar) => Some((next, arms2)),
            _ => None,
        });
        let Some((next, arms2)) = inner_match else { return unsup("for-loop desugaring") };
        // `Some { 0: pat } => body` (a struct pattern in current HIR; a tuple-struct pattern in older ones)
        let some = arms2.iter().find_map(|a| match a.pat.kind {
            PatKind::TupleStruct(_, [p], _) => Some((a, p)),
            PatKind::Struct(_, [f], _) => Some((a, f.pat)),
            _ => None,
        });
        let Some((some_arm, pat)) = some else { return unsup("for-loop desugaring") };
        // the iterable: a range, slice, array or Vec is iterated by a uRust `for` loop
        let ht = self.ty_of(head);
        // the elements not moved out by the body would be dropped (not modelled)
        if self.needs_glue(ht) {
            return unsup("`for` over values with destructors");
        }
        // over `&mut` of a slice, array or Vec (or `xs.iter_mut()`) the items are references to
        // the elements: AutoCorrode's `iter_mut`
        let mut_items = match ht.kind() {
            // a `Vec`'s elements by the reference focused on them
            ty::Ref(_, inner, m) if m.is_mut() && self.is_vec(*inner) => {
                let r = self.val(head)?;
                Some(self.vec_elems_ref(&r))
            }
            ty::Ref(_, inner, m) if m.is_mut() && self.list_like(*inner) => Some(self.val(head)?),
            _ if let Some(recv) = self.std_method_recv(head, StdFn::SliceIterMut) => Some(self.val(recv)?),
            _ => None,
        };
        let iter_s = match ht.peel_refs().kind() {
            _ if let Some(r) = mut_items => Tr::new(format!("iter_mut({})", r.at(11)), 999),
            ty::Adt(def, _) if matches!(self.fe.std_adt(def.did()), Some("Range") | Some("RangeInclusive")) => self.val(head)?,
            _ if self.is_vec(ht.peel_refs()) => {
                let v = self.val(head)?;
                self.to_val(self.vec_elems(PV::Val(v)))
            }
            _ if self.list_like(ht) => self.val(head)?,
            // `xs.iter()` over a slice, array or Vec: iterate over `xs`
            _ if let Some(recv) = self.std_method_recv(head, StdFn::SliceIter) => self.val(recv)?,
            // any other iterator, as Rust defines `for`: `let mut iter = IntoIterator::into_iter(e);
            // while let Some(p) = Iterator::next(&mut iter) { body }`
            _ => {
                // the iterator is stored in a mutable local, whose storage is chosen by its type;
                // the type is stated, as the iterator comes from polymorphic external functions
                let iter_v = self.val(head_call)?;
                let iter_ty = self.hty(self.ty_of(head_call));
                let tmp = self.fresh("iter");
                let typed = Tr::atom(format!("\\<llangle>{} :: {}\\<rrangle>", tmp, iter_ty));
                let init = format!("let {} = {};\n{}", tmp, iter_v.at(20), self.bind_pattern(arm.pat, typed)?);
                let next_v = self.val(next)?;
                let p = self.pat(some_arm.pat)?;
                if !p.conds.is_empty() { return unsup("for-loop pattern with literal or range sub-patterns") }
                let body = with_prologue(&p.prologue, &self.branch(some_arm.body)?);
                return Ok(Tr::atom(format!(
                    "{{\n{}\n{} {}while let {} = {} {{\n{}\n}}\n}}",
                    init,
                    FUEL,
                    lbl,
                    p.pat,
                    next_v.at(20),
                    body
                )));
            }
        };
        // the loop pattern
        let mut pro = vec![];
        let ps = match pat.kind {
            PatKind::Binding(bm, hid, ident, None) if let Some(m) = by_value(bm) => {
                let n = names::local_name(ident.as_str());
                let a = self.declare(hid, &n, m)?;
                if m.is_mut() {
                    pro.push(self.let_binding(&n, m, &a, &n));
                }
                n
            }
            PatKind::Wild => "_".into(),
            _ => {
                let tmp = self.fresh("item");
                pro.extend(self.irrefutable(pat, &Tr::atom(tmp.clone()))?);
                tmp
            }
        };
        let body = with_prologue(&pro, &self.branch(some_arm.body)?);
        Ok(Tr::new(format!("{}for {} in {} {{\n{}\n}}", lbl, ps, iter_s.at(20), body), 11))
    }

    // ------------------------------------------------------------------
    // match
    // ------------------------------------------------------------------

    fn int_like(&self, t: Ty<'tcx>) -> bool {
        let t = t.peel_refs();
        t.is_integral() || t.is_char() || self.str_like(t)
    }

    fn match_expr(&mut self, scrut: &'tcx hir::Expr<'tcx>, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        let st = self.ty_adj(scrut);
        let sv = self.scrut(scrut)?;
        let place = self.scrut_place(scrut)?;
        if self.int_like(st) || arms.iter().all(|a| self.chainable(a.pat)) {
            return self.match_chain(sv, arms);
        }
        let needs_split = arms
            .iter()
            .any(|a| Self::irrefutable_shape(a.pat) && (a.guard.is_some() || Self::has_lit(a.pat)));
        if !needs_split {
            let m = self.match_arms(&sv, &place, arms)?;
            return Ok(Tr::new(format!("match {} {{\n{}\n}}", sv.at(20), m), 20));
        }
        let tmp = self.fresh("scrut");
        let tv = Tr::atom(tmp.clone());
        let m = self.match_arms(&tv, &place, arms)?;
        Ok(Tr::block(format!("{{\nlet {} = {};\nmatch {} {{\n{}\n}}\n}}", tmp, sv.at(20), tmp, m)))
    }

    /// The arms of a uRust `match` on `v`. An arm whose pattern cannot fail but which has a
    /// condition (guard or literal sub-pattern) becomes a single arm whose body tests the
    /// condition and matches the remaining arms otherwise: uRust would else generate a
    /// redundant catch-all case, which HOL rejects.
    fn match_arms(&mut self, v: &Tr, place: &Option<Tr>, arms: &'tcx [hir::Arm<'tcx>]) -> R<String> {
        let mut out = vec![];
        for (i, arm) in arms.iter().enumerate() {
            // an arm rustc finds unreachable is not translated (see `reachability`)
            if crate::reachability::unreachable_arm(arm.hir_id) {
                continue;
            }
            let p = self.pat_at(arm.pat, place.clone())?;
            let mut conds = p.conds.clone();
            if let Some(g) = arm.guard {
                if contains_let(g) {
                    return unsup("`if let` guard");
                }
                let gv = self.val(g)?;
                // the guard may use the bindings by mutable reference
                conds.push(if p.refs.is_empty() { gv.at(44) } else { format!("{{ {} {} }}", p.refs.join(" "), gv.at(20)) });
            }
            let irref = Self::irrefutable_shape(arm.pat);
            if irref && !conds.is_empty() {
                let rest = if i + 1 < arms.len() {
                    format!("match {} {{\n{}\n}}", v.at(20), self.match_arms(v, place, &arms[i + 1..])?)
                } else {
                    "panic!(\"non-exhaustive match\")".to_string()
                };
                let then = self.branch(arm.body)?;
                let body = with_prologue(&p.prologue, &format!("if {} {{\n{}\n}} else {{\n{}\n}}", conds.join(" && "), then, rest));
                out.push(format!("  {} \\<Rightarrow> {{\n{}\n}}", p.pat, body));
                break;
            }
            let body = with_prologue(&p.prologue, &self.branch(arm.body)?);
            let guard = if conds.is_empty() { String::new() } else { format!(" if {}", conds.join(" && ")) };
            out.push(format!("  {}{} \\<Rightarrow> {{\n{}\n}}", p.pat, guard, body));
            if irref {
                break; // later arms are unreachable
            }
        }
        Ok(out.join(",\n"))
    }

    /// Patterns that match every value of their type once literal sub-patterns are turned
    /// into conditions: wildcards, bindings, literals, ranges and tuples of such.
    fn irrefutable_shape(p: &'tcx hir::Pat<'tcx>) -> bool {
        match p.kind {
            PatKind::Wild | PatKind::Range(..) => true,
            PatKind::Expr(pe) => matches!(pe.kind, hir::PatExprKind::Lit { .. }),
            PatKind::Binding(_, _, _, sub) => sub.map(Self::irrefutable_shape).unwrap_or(true),
            PatKind::Tuple(ps, _) => ps.iter().all(Self::irrefutable_shape),
            PatKind::Ref(q, _, _) | PatKind::Deref(q) => Self::irrefutable_shape(q),
            _ => false,
        }
    }

    fn has_lit(p: &'tcx hir::Pat<'tcx>) -> bool {
        match p.kind {
            PatKind::Range(..) => true,
            PatKind::Expr(pe) => matches!(pe.kind, hir::PatExprKind::Lit { .. }),
            PatKind::Binding(_, _, _, Some(s)) => Self::has_lit(s),
            PatKind::Tuple(ps, _) => ps.iter().any(Self::has_lit),
            PatKind::Ref(q, _, _) | PatKind::Deref(q) => Self::has_lit(q),
            _ => false,
        }
    }

    /// Patterns handled by the `if`-chain translation (`pat_cond`).
    fn chainable(&self, p: &'tcx hir::Pat<'tcx>) -> bool {
        match p.kind {
            PatKind::Wild | PatKind::Range(..) => true,
            PatKind::Expr(pe) => match pe.kind {
                hir::PatExprKind::Lit { .. } => true,
                hir::PatExprKind::Path(ref qp) => match self.typeck.qpath_res(qp, pe.hir_id) {
                    Res::Def(DefKind::Ctor(CtorOf::Variant, CtorKind::Const), c) => {
                        self.fe.std_adt(self.ctor_variant(CtorOf::Variant, c).0) == Some("Ordering")
                    }
                    Res::Def(DefKind::Const | DefKind::AssocConst { .. }, _) => true,
                    _ => false,
                },
            },
            PatKind::Binding(bm, _, _, sub) if by_value(bm).is_some() => {
                sub.map(|s| self.chainable(s)).unwrap_or(true)
            }
            PatKind::Or(ps) | PatKind::Tuple(ps, _) => ps.iter().all(|q| self.chainable(q)),
            PatKind::Ref(q, _, _) | PatKind::Deref(q) => self.chainable(q),
            _ => false,
        }
    }

    /// `match` on integers / chars / strings as an `if` chain.
    fn match_chain(&mut self, sv: Tr, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        let tmp = self.fresh("scrut");
        let tv = Tr::atom(tmp.clone());
        let mut branches: Vec<(Option<String>, String)> = vec![];
        for arm in arms {
            let (cond, binds) = self.pat_cond(arm.pat, &tv)?;
            let body = with_prologue(&binds, &self.branch(arm.body)?);
            let cond = match arm.guard {
                Some(g) => {
                    if contains_let(g) { return unsup("`if let` guard") }
                    let gv = self.val(g)?;
                    let gblock = if binds.is_empty() { gv.at(44) } else { format!("{{ {}\n{} }}", binds.join("\n"), gv.s) };
                    Some(match cond { Some(c) => format!("{} && {}", paren_if(&c), gblock), None => gblock })
                }
                None => cond,
            };
            branches.push((cond, body));
        }
        let acc = if_chain(branches);
        Ok(Tr::block(format!("{{\nlet {} = {};\n{}\n}}", tmp, sv.at(20), acc)))
    }

    /// Condition + bindings for a pattern matched against a value (used for scalar matches).
    fn pat_cond(&mut self, pat: &'tcx hir::Pat<'tcx>, v: &Tr) -> R<(Option<String>, Vec<String>)> {
        match pat.kind {
            PatKind::Wild => Ok((None, vec![])),
            PatKind::Binding(bm, hid, ident, sub) if let Some(m) = by_value(bm) => {
                let n = names::local_name(ident.as_str());
                let a = self.declare(hid, &n, m)?;
                let mut binds = vec![self.let_binding(&n, m, &a, &v.at(20))];
                match sub {
                    Some(s) => {
                        let (c, b2) = self.pat_cond(s, v)?;
                        binds.extend(b2);
                        Ok((c, binds))
                    }
                    None => Ok((None, binds)),
                }
            }
            PatKind::Binding(..) => unsup("`ref mut` binding"),
            PatKind::Expr(pe) => Ok((Some(format!("{} == {}", v.at(45), self.pat_expr(pe, pat)?.at(45))), vec![])),
            PatKind::Range(lo, hi, end) => {
                let cs = self.range_conds(lo, hi, end, pat, &v.at(45))?;
                Ok((Some(cs.into_iter().map(|c| format!("({})", c)).collect::<Vec<_>>().join(" && ")), vec![]))
            }
            PatKind::Or(ps) => {
                let mut cs = vec![];
                for p in ps.iter() {
                    let (c, b) = self.pat_cond(p, v)?;
                    if !b.is_empty() { return unsup("or-pattern with bindings") }
                    match c { Some(c) => cs.push(format!("({})", c)), None => return Ok((None, vec![])) }
                }
                Ok((Some(cs.join(" || ")), vec![]))
            }
            PatKind::Tuple(ps, ddpos) => {
                let t = self.pat_ty(pat).peel_refs();
                let n = match t.kind() { ty::Tuple(ts) => ts.len(), _ => ps.len() };
                if n > 16 { return unsup("tuple with more than 16 components") }
                let mut cs = vec![];
                let mut binds = vec![];
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    if let Some(p) = p {
                        let proj = Tr::new(format!("{}.{}", v.at(998), k), 998);
                        let (c, b) = self.pat_cond(p, &proj)?;
                        if let Some(c) = c { cs.push(format!("({})", c)); }
                        binds.extend(b);
                    }
                }
                Ok((if cs.is_empty() { None } else { Some(cs.join(" && ")) }, binds))
            }
            PatKind::Ref(p, _, _) | PatKind::Deref(p) => self.pat_cond(p, v),
            _ => unsup("pattern in a match on a scalar"),
        }
    }

    /// The conditions of the range pattern `lo..hi` / `lo..=hi` (in `pat`) on the value `v`.
    fn range_conds(
        &mut self,
        lo: Option<&'tcx hir::PatExpr<'tcx>>,
        hi: Option<&'tcx hir::PatExpr<'tcx>>,
        end: hir::RangeEnd,
        pat: &'tcx hir::Pat<'tcx>,
        v: &str,
    ) -> R<Vec<String>> {
        let mut cs = vec![];
        if let Some(lo) = lo {
            cs.push(format!("{} <= {}", self.pat_expr(lo, pat)?.at(45), v));
        }
        if let Some(hi) = hi {
            let op = if matches!(end, hir::RangeEnd::Included) { "<=" } else { "<" };
            cs.push(format!("{} {} {}", v, op, self.pat_expr(hi, pat)?.at(45)));
        }
        Ok(cs)
    }

    /// A literal / constant inside a pattern, as a uRust value.
    fn pat_expr(&mut self, pe: &'tcx hir::PatExpr<'tcx>, pat: &'tcx hir::Pat<'tcx>) -> R<Tr> {
        let t = self.node_ty(pe.hir_id).peel_refs();
        let t = if t.is_integral() || t.is_char() || t.is_bool() || t.is_str() { t } else { self.pat_ty(pat).peel_refs() };
        match pe.kind {
            hir::PatExprKind::Lit { lit, negated } => {
                match lit.node {
                    LitKind::Int(v, _) => Self::int_lit(v.get(), negated, t),
                    _ if negated => unsup(format!("negative literal pattern of type `{}`", t)),
                    _ => self.lit(&lit.node, t),
                }
            }
            hir::PatExprKind::Path(ref qp) => match self.typeck.qpath_res(qp, pe.hir_id) {
                Res::Def(DefKind::Const | DefKind::AssocConst { .. }, did) => {
                    self.scalar_const(did, t).unwrap_or_else(|| unsup("constant in pattern"))
                }
                Res::Def(DefKind::Ctor(of, CtorKind::Const), c) => {
                    let (adt, vidx) = self.ctor_variant(of, c);
                    self.unit_ctor(adt, vidx)
                }
                _ => unsup("path in pattern expression"),
            },
        }
    }

    /// Translate a refutable pattern for a uRust `match` / `if let`.
    fn pat(&mut self, pat: &'tcx hir::Pat<'tcx>) -> R<PatTr> {
        let mut conds = vec![];
        let mut prologue = vec![];
        let place = self.match_place.clone();
        self.pat_refs.clear();
        let s = self.pat_rec(pat, &mut conds, &mut prologue, place)?;
        let refs = std::mem::take(&mut self.pat_refs);
        Ok(PatTr { pat: s, conds, prologue, refs })
    }

    /// `pat` matching a value behind the mutable reference `place` (see `scrut_place`).
    fn pat_at(&mut self, pat: &'tcx hir::Pat<'tcx>, place: Option<Tr>) -> R<PatTr> {
        self.match_place = place;
        let r = self.pat(pat);
        self.match_place = None;
        r
    }

    /// The mutable reference a scrutinee `e` of type `&mut T` evaluates to, when evaluating it
    /// again has no effect (a pattern binding by mutable reference is focused into it).
    fn scrut_place(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Option<Tr>> {
        let simple = match e.kind {
            ExprKind::AddrOf(_, hir::Mutability::Mut, inner) => self.is_simple(inner),
            _ => self.is_simple(e),
        };
        match self.ty_adj(e).kind() {
            ty::Ref(_, inner, m) if m.is_mut() && !inner.is_ref() && simple => Ok(Some(self.val(e)?)),
            _ => Ok(None),
        }
    }

    /// The reference to component `k` of the value of type `t` behind the reference `r`: a field
    /// of a local struct translated as a record, or a tuple component.
    fn place_field(&mut self, r: &Tr, t: Ty<'tcx>, k: usize) -> Option<Tr> {
        match t.kind() {
            ty::Adt(def, _) if def.is_struct() && def.did().is_local() && self.fe.record_adts.contains(&def.did()) => {
                Some(Tr::new(format!("{}.{}", r.at(99), self.fe.field_name(def.did(), 0, k)), 100))
            }
            ty::Tuple(ts) if ts.len() <= 16 => {
                let lens = vec!["snd\\<^sub>L"; k].into_iter().chain(["fst\\<^sub>L"]).collect::<Vec<_>>().join(" \\<circ>\\<^sub>L ");
                Some(Tr::new(format!("\\<llangle>focus_reference_via_lens ({})\\<rrangle>\\<^sub>1({})", lens, r.s), 999))
            }
            _ => None,
        }
    }

    /// `place`: the mutable reference to the value matched by `pat`, if known (see `scrut_place`).
    fn pat_rec(&mut self, pat: &'tcx hir::Pat<'tcx>, conds: &mut Vec<String>, pro: &mut Vec<String>, place: Option<Tr>) -> R<String> {
        // a binding by mutable reference (`ref mut x`, or after match ergonomics): the reference
        // focused to the matched part, bound before the arm's body; the pattern does not bind
        if let PatKind::Binding(_, hid, ident, sub) = pat.kind
            && let Some(hir::BindingMode(hir::ByRef::Yes(_, mutbl), _)) = self.typeck.pat_binding_modes().get(hid)
            && mutbl.is_mut()
        {
            let (Some(r), None) = (place, sub) else { return unsup("binding by mutable reference (match ergonomics)") };
            let n = names::local_name(ident.as_str());
            self.declare(hid, &n, hir::Mutability::Not)?;
            let b = format!("let {} = {};", n, r.at(20));
            self.pat_refs.push(b.clone());
            pro.push(b);
            return Ok("_".into());
        }
        match pat.kind {
            PatKind::Wild => Ok("_".into()),
            PatKind::Binding(bm, hid, ident, sub) if let Some(m) = by_value(bm) => {
                let n = names::local_name(ident.as_str());
                let a = self.declare(hid, &n, m)?;
                if m.is_mut() {
                    pro.push(self.let_binding(&n, m, &a, &n));
                }
                match sub {
                    None => Ok(n),
                    Some(s) if matches!(s.kind, PatKind::Range(..))
                        || matches!(s.kind, PatKind::Expr(pe) if matches!(pe.kind, hir::PatExprKind::Lit { .. })) =>
                    {
                        // `n @ 1..=9`: put the condition on `n` itself
                        let (c, _) = self.pat_cond(s, &Tr::atom(n.clone()))?;
                        if let Some(c) = c {
                            conds.push(format!("({})", c));
                        }
                        Ok(n)
                    }
                    Some(s) => {
                        let inner = self.pat_rec(s, conds, pro, None)?;
                        Ok(format!("{} @ {}", n, if inner.contains(' ') { format!("({})", inner) } else { inner }))
                    }
                }
            }
            PatKind::Binding(..) => unsup("`ref mut` binding"),
            PatKind::Tuple(ps, ddpos) => {
                let t = self.pat_ty(pat).peel_refs();
                let n = match t.kind() { ty::Tuple(ts) => ts.len(), _ => ps.len() };
                if n < 2 { return unsup("tuple pattern with fewer than 2 components") }
                let mut parts = vec![];
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    let pl = place.as_ref().and_then(|r| self.place_field(r, t, k));
                    parts.push(match p { Some(p) => self.pat_rec(p, conds, pro, pl)?, None => "_".into() });
                }
                Ok(format!("({})", parts.join(", ")))
            }
            PatKind::TupleStruct(ref qp, ps, ddpos) => {
                let (adt, vidx) = self.pat_variant(qp, pat)?;
                let t = self.pat_ty(pat).peel_refs();
                let n = self.tcx.adt_def(adt).variant(vidx.into()).fields.len();
                let mut parts = vec![];
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    // into `Some`: AutoCorrode's `focus_option`; into a struct: its field
                    let pl = place.as_ref().and_then(|r| {
                        if self.fe.std_adt(adt) == Some("Option") {
                            Some(Tr::new(format!("\\<llangle>focus_option\\<rrangle>\\<^sub>1({})", r.s), 999))
                        } else {
                            self.place_field(r, t, k)
                        }
                    });
                    parts.push(match p { Some(p) => self.pat_rec(p, conds, pro, pl)?, None => "_".into() });
                }
                self.ctor_pat(adt, vidx, parts)
            }
            PatKind::Struct(ref qp, fields, _) => {
                let (adt, vidx) = self.pat_variant(qp, pat)?;
                let t = self.pat_ty(pat).peel_refs();
                let n = self.tcx.adt_def(adt).variant(vidx.into()).fields.len();
                let mut parts = vec!["_".to_string(); n];
                for f in fields.iter() {
                    let idx = self.typeck.field_index(f.hir_id).as_usize();
                    let pl = place.as_ref().and_then(|r| self.place_field(r, t, idx));
                    parts[idx] = self.pat_rec(f.pat, conds, pro, pl)?;
                }
                self.ctor_pat(adt, vidx, parts)
            }
            PatKind::Expr(pe) => {
                if let hir::PatExprKind::Path(ref qp) = pe.kind
                    && let Res::Def(DefKind::Ctor(of, CtorKind::Const), ctor) = self.typeck.qpath_res(qp, pe.hir_id)
                {
                    let (adt, vidx) = self.ctor_variant(of, ctor);
                    return self.ctor_pat(adt, vidx, vec![]);
                }
                let v = self.pat_expr(pe, pat)?;
                let tmp = self.fresh("lit");
                conds.push(format!("{} == {}", tmp, v.at(45)));
                Ok(tmp)
            }
            PatKind::Range(lo, hi, end) => {
                let tmp = self.fresh("rng");
                conds.extend(self.range_conds(lo, hi, end, pat, &tmp)?);
                Ok(tmp)
            }
            PatKind::Or(ps) => {
                let mut parts = vec![];
                for p in ps.iter() {
                    let mut c2 = vec![];
                    let mut p2 = vec![];
                    parts.push(self.pat_rec(p, &mut c2, &mut p2, None)?);
                    if !c2.is_empty() || !p2.is_empty() { return unsup("or-pattern with literal sub-patterns or mutable bindings") }
                }
                Ok(parts.join(" | "))
            }
            PatKind::Ref(p, _, _) | PatKind::Deref(p) => self.pat_rec(p, conds, pro, place),
            PatKind::Slice(before, None, after) if after.is_empty() => {
                let t = self.pat_ty(pat).peel_refs();
                if !matches!(t.kind(), ty::Slice(_) | ty::Array(..)) { return unsup("slice pattern") }
                let mut parts = vec![];
                for p in before.iter() { parts.push(self.pat_rec(p, conds, pro, None)?); }
                Ok(format!("[{}]", parts.join(", ")))
            }
            PatKind::Slice(..) => unsup("slice pattern with a rest pattern"),
            PatKind::Never => unsup("never pattern"),
            PatKind::Guard(..) => unsup("guard pattern"),
            PatKind::Missing | PatKind::Err(_) => unsup("pattern"),
        }
    }

    fn pat_variant(&mut self, qp: &'tcx hir::QPath<'tcx>, pat: &'tcx hir::Pat<'tcx>) -> R<(DefId, usize)> {
        let t = self.pat_ty(pat).peel_refs();
        let ty::Adt(def, _) = t.kind() else { return unsup("constructor pattern on non-ADT") };
        let v = def.variant_of_res(self.typeck.qpath_res(qp, pat.hir_id));
        Ok((def.did(), def.variant_index_with_id(v.def_id).as_usize()))
    }

    fn ctor_pat(&mut self, adt: DefId, vidx: usize, parts: Vec<String>) -> R<String> {
        self.opaque_adt(adt)?;
        let name = match self.fe.std_adt(adt) {
            Some("Option") | Some("Result") | Some("Ordering") => self.tcx.adt_def(adt).variant(vidx.into()).name.to_string(),
            Some("Box") => return parts.into_iter().next().ok_or(Unsup("box pattern".into())),
            Some(_) => return unsup("pattern on a standard library type"),
            None if !adt.is_local() => match self.fe.ext_ctor(adt, vidx) {
                Some((c, _)) => c,
                None => return unsup("pattern on an external type"),
            },
            None => self.fe.variant_ctor_name(adt, vidx),
        };
        if parts.is_empty() { Ok(name) } else { Ok(format!("{}({})", name, parts.join(", "))) }
    }

    // ------------------------------------------------------------------
    // Closures
    // ------------------------------------------------------------------

    fn closure(&mut self, e: &'tcx hir::Expr<'tcx>, c: &'tcx hir::Closure<'tcx>) -> R<Tr> {
        if !matches!(c.kind, hir::ClosureKind::Closure) { return unsup("async block / coroutine") }
        // a closure mutates a captured variable if it captures it by a mutable (or unique) borrow,
        // or its body mutates a variable it captures by value (its own copy). The closure kind
        // does not tell: it is taken from the expected `Fn*` bound when there is one
        let captured: HashSet<HirId> =
            self.typeck.closure_min_captures_flattened(c.def_id).map(|cap| cap.get_root_variable()).collect();
        let mut finder = CaptureMutation { typeck: self.typeck, captured: &captured, found: false };
        finder.visit_body(self.tcx.hir_body(c.body));
        if finder.found {
            return unsup("closure that mutates captured variables");
        }
        let mut copies = vec![];
        let mut saved = vec![];
        for cap in self.typeck.closure_min_captures_flattened(c.def_id) {
            match cap.info.capture_kind {
                ty::UpvarCapture::ByRef(k) => {
                    if !matches!(k, ty::BorrowKind::Immutable) {
                        return unsup("closure that mutates captured variables");
                    }
                }
                // a variable captured by value is copied when the closure is created: a mutable
                // local is read then, and the closure body sees the (immutable) copy
                ty::UpvarCapture::ByValue | ty::UpvarCapture::ByUse => {
                    let root = cap.get_root_variable();
                    if saved.iter().any(|(h, _)| *h == root) { continue }
                    let l = self.locals.get(&root).cloned().expect("captured variable is a local of the enclosing body");
                    if !l.cell { continue }
                    let n = self.fresh(&format!("{}_copy", l.name));
                    copies.push(format!("let {} = * {};", n, l.name));
                    self.locals.insert(root, Local { name: n, cell: false });
                    saved.push((root, l));
                }
            }
        }
        let r = self.closure_body(c);
        for (h, l) in saved {
            self.locals.insert(h, l);
        }
        let (ps, b) = r?;
        let head = if ps.is_empty() { "||".to_string() } else { format!("|{}|", ps.join(", ")) };
        let closure = Tr::new(format!("{} {{\n{}\n}}", head, b), 10);
        // the closure runs in the monad of the enclosing function: its type is stated, as nothing
        // else fixes it when it is only passed to a polymorphic external function (placeholder
        // types are declared HOL types, so they may occur in it)
        let h = self.hty(self.ty_of(e));
        let tmp = self.fresh("closure");
        copies.push(format!("let {} = {};", tmp, closure.at(20)));
        Ok(Tr::block(format!("{{ {} \\<llangle>{} :: {}\\<rrangle> }}", copies.join(" "), tmp, h)))
    }

    /// `c.encode_utf8(buf).as_bytes()`: `char_encode_utf8_bytes(c, buf)`, the bytes of the encoding,
    /// also written to the buffer; the `&mut str` in between (a reference into the buffer, which
    /// has no model) is not kept. `None` for other calls.
    fn encode_utf8_bytes(&mut self, did: DefId, recv: &'tcx hir::Expr<'tcx>) -> R<Option<Tr>> {
        if self.std_fn(did) != Some(StdFn::Model("str_as_bytes")) { return Ok(None) }
        let ExprKind::MethodCall(_, c, [buf], _) = recv.kind else { return Ok(None) };
        let Some(inner) = self.typeck.type_dependent_def_id(recv.hir_id) else { return Ok(None) };
        if self.std_fn(inner) != Some(StdFn::CharEncodeUtf8) { return Ok(None) }
        let argv = self.vals([c, buf])?;
        Ok(Some(self.named_call("char_encode_utf8_bytes", argv)))
    }

    /// A tuple-like constructor used as a function value: the closure calling it (as for function
    /// items, see `fn_item_value`).
    fn ctor_value(&mut self, of: CtorOf, ctor: DefId, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let tcx = self.tcx;
        let (adt, vidx) = self.ctor_variant(of, ctor);
        let ty::FnDef(..) = self.ty_of(e).kind() else { return unsup("constructor used as a function value") };
        let sig = tcx.instantiate_bound_regions_with_erased(self.ty_of(e).fn_sig(tcx));
        let ps: Vec<String> = sig.inputs().iter().map(|_| self.fresh("carg")).collect();
        let tys: Vec<String> = sig.inputs().iter().map(|t| self.hty(*t)).collect();
        let ret = self.hty(sig.output());
        let call = self.ctor_call(adt, vidx, ps.iter().map(|p| Tr::atom(p.clone())).collect())?;
        let head = if ps.is_empty() { "||".to_string() } else { format!("|{}|", ps.join(", ")) };
        let h = self.fe.fun_type(&tys, &ret);
        let tmp = self.fresh("closure");
        Ok(Tr::block(format!("{{ let {} = ( {} {{\n{}\n}}); \\<llangle>{} :: {}\\<rrangle> }}", tmp, head, call.s, tmp, h)))
    }

    /// A function item `f` used as a value: the closure `|a1, .., an| f(a1, .., an)` (for a
    /// local function, or a trait method resolved to a local implementation), with its type
    /// stated as for closures.
    fn fn_item_value(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let tcx = self.tcx;
        let ty::FnDef(did, gargs) = *self.ty_of(e).kind() else { return unsup("function item used as a value") };
        let gargs = tcx.instantiate_bound_regions_with_erased(gargs);
        let (target, targs) = if self.fe.is_trait_item(did) {
            match self.resolve_instance(did, gargs) {
                Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), args })) => (rd, args),
                _ => return unsup("function item used as a value"),
            }
        } else {
            (did, gargs)
        };
        if !(target.is_local() && self.fe.local_fn_with_body(target) && !self.derived(target)) {
            return unsup("function item used as a value");
        }
        let sig = tcx.instantiate_bound_regions_with_erased(self.ty_of(e).fn_sig(tcx));
        let ps: Vec<String> = sig.inputs().iter().map(|_| self.fresh("farg")).collect();
        let tys: Vec<String> = sig.inputs().iter().map(|t| self.hty(*t)).collect();
        let ret = self.hty(sig.output());
        let call = self.local_call(target, targs, ps.iter().map(|p| Tr::atom(p.clone())).collect())?;
        let head = if ps.is_empty() { "||".to_string() } else { format!("|{}|", ps.join(", ")) };
        let h = self.fe.fun_type(&tys, &ret);
        let tmp = self.fresh("closure");
        Ok(Tr::block(format!("{{ let {} = ( {} {{\n{}\n}}); \\<llangle>{} :: {}\\<rrangle> }}", tmp, head, call.s, tmp, h)))
    }

    /// The formals and the body of a closure.
    fn closure_body(&mut self, c: &'tcx hir::Closure<'tcx>) -> R<(Vec<String>, String)> {
        self.drop_scopes.push(DropScope::Body(vec![]));
        let r = self.closure_body_scoped(c);
        self.drop_scopes.pop();
        r
    }

    fn closure_body_scoped(&mut self, c: &'tcx hir::Closure<'tcx>) -> R<(Vec<String>, String)> {
        let body = self.tcx.hir_body(c.body);
        let mut ps = vec![];
        let mut pro = vec![];
        for (i, p) in body.params.iter().enumerate() {
            match p.pat.kind {
                PatKind::Binding(bm, hid, ident, None) if let Some(m) = by_value(bm) => {
                    let n = names::local_name(ident.as_str());
                    // closure formals carry no type in uRust: fix it in the body
                    let (pt, modelled) = self.fe.ty_modelled(self.node_ty(hid));
                    if modelled {
                        pro.push(format!("let {} = \\<llangle>{} :: {}\\<rrangle>;", n, n, pt));
                    }
                    let a = self.declare_owned(hid, &n, m)?;
                    if m.is_mut() {
                        pro.push(self.let_binding(&n, m, &a, &n));
                    }
                    pro.extend(self.own(hid, true)?);
                    ps.push(n);
                }
                _ if self.needs_glue(self.pat_ty(p.pat)) => return unsup("parameter with a destructor bound by a pattern"),
                _ => {
                    let n = format!("carg_{}", i);
                    pro.extend(self.irrefutable(p.pat, &Tr::atom(n.clone()))?);
                    ps.push(n);
                }
            }
        }
        let b = self.block_expr_inner(body.value)?;
        let b = self.with_body_drops(b)?;
        Ok((ps, with_prologue(&pro, &b)))
    }

    // ------------------------------------------------------------------
    // Destructors
    // ------------------------------------------------------------------

    /// Whether dropping a value of type `t` runs a destructor of the crate (`Drop` implemented
    /// for a local type), for the value itself or for its fields, contents or elements. A type
    /// parameter runs none: a generic version is translated for the types without destructors
    /// (as the standard library's, whose destructors only free memory); within the crate, the
    /// functions binding values of such types are also translated per instance (see
    /// `translate::GenericCalls`).
    fn needs_glue(&self, t: Ty<'tcx>) -> bool {
        if !self.fe.has_drop_impls { return false }
        if let Some(&r) = self.glue_cache.borrow().get(&t) { return r }
        let r = self.glue_in(t, &mut HashSet::new());
        self.glue_cache.borrow_mut().insert(t, r);
        r
    }

    /// `t` normalised, with an `impl Trait` type replaced by its hidden type (see
    /// `frontend::try_normalize`).
    fn reveal(&self, t: Ty<'tcx>) -> Ty<'tcx> {
        crate::frontend::try_normalize(self.tcx, self.typing_env(), ty::Unnormalized::new_wip(t)).unwrap_or(t)
    }

    /// Whether a type reachable from `t` (through fields, contents, elements, captures) has a
    /// destructor of the crate, by a depth-first search over the types not in `seen`. A type
    /// already visited is not explored again: either it reached no destructor, or it is still
    /// being explored by a caller, which then answers for it. (Unvisiting a type on the way back
    /// would explore it again on every path to it: exponential in mutually recursive types that
    /// share fields, as sqlparser's syntax tree.)
    fn glue_in(&self, t: Ty<'tcx>, seen: &mut HashSet<Ty<'tcx>>) -> bool {
        let t = self.reveal(t);
        if !seen.insert(t) { return false }
        match t.kind() {
            ty::Adt(d, args) if d.did().is_local() => {
                self.tcx.adt_destructor(d.did()).is_some()
                    || d.all_fields().any(|f| self.glue_in(f.ty(self.tcx, args).skip_normalization(), seen))
            }
            // a standard type: one with a destructor drops what its type arguments own (a
            // `Vec`, a `Box`, ...); one without drops its fields (an iterator over borrowed
            // elements holds pointers, which own nothing)
            ty::Adt(d, args) if self.tcx.adt_destructor(d.did()).is_some() => args.types().any(|x| self.glue_in(x, seen)),
            ty::Adt(d, args) => d.all_fields().any(|f| self.glue_in(f.ty(self.tcx, args).skip_normalization(), seen)),
            ty::Tuple(ts) => ts.iter().any(|x| self.glue_in(x, seen)),
            ty::Array(x, _) | ty::Slice(x) => self.glue_in(*x, seen),
            ty::Closure(_, a) => a.as_closure().upvar_tys().iter().any(|x| self.glue_in(x, seen)),
            _ => false,
        }
    }

    /// The statements dropping the value `pv` of type `t` (Rust's drop glue): for a local struct
    /// with a `Drop` implementation, its `drop` on a reference to the value, then the fields in
    /// declaration order; the contents of a `Box` or an `Option`, the components of a tuple, the
    /// elements of a sequence in order.
    fn drop_glue(&mut self, t: Ty<'tcx>, pv: PV) -> R<Vec<String>> {
        if !self.needs_glue(t) { return Ok(vec![]) }
        let rt = self.reveal(t);
        if self.glue_stack.contains(&rt) { return unsup("destructor of a recursive type") }
        self.glue_stack.push(rt);
        let r = self.drop_glue_unrolled(t, pv);
        self.glue_stack.pop();
        r
    }

    fn drop_glue_unrolled(&mut self, t: Ty<'tcx>, pv: PV) -> R<Vec<String>> {
        let tcx = self.tcx;
        let t = self.reveal(t);
        let mut out = vec![];
        match t.kind() {
            ty::Adt(d, args) if d.is_box() => return self.drop_glue(args.type_at(0), pv),
            ty::Adt(d, args) if d.did().is_local() && d.is_struct() => {
                let adt = d.did();
                let mut pv = pv;
                if tcx.adt_destructor(adt).is_some() {
                    let r = match pv {
                        PV::Ref(r) => r,
                        PV::Val(v) => {
                            let a = self.alloc(t)?;
                            let tmp = self.fresh("dropped");
                            out.push(self.let_binding(&tmp, hir::Mutability::Mut, &a, &v.at(20)));
                            Tr::atom(tmp)
                        }
                    };
                    let drop_trait = tcx.lang_items().drop_trait().ok_or(Unsup("`Drop` trait".into()))?;
                    let Some(m) = tcx.associated_items(drop_trait).in_definition_order().next().map(|i| i.def_id) else {
                        return unsup("`Drop::drop`");
                    };
                    let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(rd), args: rargs })) =
                        self.resolve_instance(m, tcx.mk_args(&[t.into()]))
                    else {
                        return unsup(format!("destructor of `{}`", t));
                    };
                    let call = self.local_call(rd, rargs, vec![r.clone()])?;
                    out.push(format!("{};", call.at(11)));
                    pv = PV::Ref(r);
                }
                for (i, f) in d.all_fields().enumerate() {
                    let ft = f.ty(tcx, args).skip_normalization();
                    if !self.needs_glue(ft) { continue }
                    let fpv = match &pv {
                        PV::Val(v) => PV::Val(self.field_read(adt, i, v)?),
                        PV::Ref(r) => {
                            self.opaque_adt(adt)?;
                            if !self.fe.record_adts.contains(&adt) {
                                return unsup("destructor of a field of a recursive struct");
                            }
                            PV::Ref(Tr::new(format!("{}.{}", r.at(99), self.fe.field_name(adt, 0, i)), 100))
                        }
                    };
                    out.extend(self.drop_glue(ft, fpv)?);
                }
            }
            ty::Adt(d, args) if self.fe.std_adt(d.did()) == Some("Option") => {
                let x = self.fresh("dropped");
                let inner = self.drop_glue(args.type_at(0), PV::Val(Tr::atom(x.clone())))?;
                out.push(format!("if let Some({}) = {} {{\n{}\n}} else {{\n()\n}};", x, self.to_val(pv).at(20), inner.join("\n")));
            }
            ty::Tuple(ts) => {
                let tmp = self.fresh("dropped");
                out.push(format!("let {} = {};", tmp, self.to_val(pv).at(20)));
                for (k, x) in ts.iter().enumerate() {
                    out.extend(self.drop_glue(x, PV::Val(Tr::new(format!("{}.{}", tmp, k), 998)))?);
                }
            }
            ty::Array(x, _) | ty::Slice(x) => {
                let e = self.fresh("dropped");
                let inner = self.drop_glue(*x, PV::Val(Tr::atom(e.clone())))?;
                out.push(format!("for {} in {} {{\n{}\n}};", e, self.to_val(pv).at(20), inner.join("\n")));
            }
            ty::Adt(d, args) if self.fe.std_adt(d.did()) == Some("Vec") => {
                let e = self.fresh("dropped");
                let inner = self.drop_glue(args.type_at(0), PV::Val(Tr::atom(e.clone())))?;
                let elems = self.vec_elems(PV::Val(self.to_val(pv)));
                out.push(format!("for {} in {} {{\n{}\n}};", e, self.to_val(elems).at(20), inner.join("\n")));
            }
            _ => return unsup(format!("destructor of a value of type `{}`", t)),
        }
        Ok(out)
    }

    /// The statements dropping the locals `ls` (in reverse order of declaration; one with a flag
    /// only if it holds a value).
    fn drop_locals(&mut self, ls: &[DropLocal<'tcx>]) -> R<Vec<String>> {
        let mut out = vec![];
        for l in ls.iter().rev() {
            let pv = if l.cell { PV::Ref(Tr::atom(l.name.clone())) } else { PV::Val(Tr::atom(l.name.clone())) };
            let g = self.drop_glue(l.ty, pv)?;
            if g.is_empty() { continue }
            match &l.flag {
                Some(f) => out.push(format!("if * {} {{\n{}\n}} else {{\n()\n}};", f, g.join("\n"))),
                None => out.extend(g),
            }
        }
        Ok(out)
    }

    /// Whether, when the early exit `e` (`return`, `?`, `break`, `continue`) is reached, an
    /// operand with a destructor was already evaluated by an enclosing expression (e.g. `l` in
    /// `Pair { first: l, n: x? }`): Rust drops it, which is not modelled. Conservative: every
    /// other operand of the enclosing expressions counts, up to the body or closure.
    fn exit_after_owned_operand(&self, e: &'tcx hir::Expr<'tcx>) -> bool {
        if !self.fe.has_drop_impls { return false }
        let mut child = e.hir_id;
        for (h, node) in self.tcx.hir_parent_iter(e.hir_id) {
            let hir::Node::Expr(a) = node else {
                if matches!(node, hir::Node::Item(_) | hir::Node::ImplItem(_) | hir::Node::TraitItem(_)) { break }
                child = h;
                continue;
            };
            let operands: Vec<&'tcx hir::Expr<'tcx>> = match a.kind {
                ExprKind::Closure(_) => break,
                ExprKind::Call(f, args) => std::iter::once(f).chain(args).collect(),
                ExprKind::MethodCall(_, r, args, _) => std::iter::once(r).chain(args).collect(),
                ExprKind::Tup(xs) | ExprKind::Array(xs) => xs.iter().collect(),
                ExprKind::Struct(_, fs, tail) => {
                    let mut v: Vec<_> = fs.iter().map(|f| f.expr).collect();
                    if let hir::StructTailExpr::Base(b) = tail { v.push(b) }
                    v
                }
                ExprKind::Binary(_, l, r) | ExprKind::Assign(l, r, _) | ExprKind::AssignOp(_, l, r) | ExprKind::Index(l, r, _) => vec![l, r],
                // a place matched is not moved (its scope drops it)
                ExprKind::Match(sc, _, _) if !is_place_expr(self.typeck, sc) => vec![sc],
                ExprKind::If(c, _, _) => vec![c],
                _ => vec![],
            };
            if operands.iter().any(|o| o.hir_id != child && self.needs_glue(self.ty_adj(o))) {
                return true;
            }
            child = h;
        }
        false
    }

    /// The drops when control leaves the scopes up to the loop `target` (`break`, `continue`), or
    /// up to and including the function's or closure's body (`None`: `return`), innermost first.
    fn exit_drops(&mut self, target: Option<HirId>) -> R<Vec<String>> {
        let mut ls: Vec<Vec<DropLocal<'tcx>>> = vec![];
        let mut found = false;
        for sc in self.drop_scopes.iter().rev() {
            match (sc, target) {
                (DropScope::Loop(h), Some(t)) if *h == t => {
                    found = true;
                    break;
                }
                (DropScope::Body(l), None) => {
                    ls.push(l.clone());
                    found = true;
                    break;
                }
                (DropScope::Body(_), Some(_)) => break,
                (DropScope::Block(l), _) => ls.push(l.clone()),
                (DropScope::Loop(_), _) => {}
            }
        }
        let mut out = vec![];
        for l in ls {
            out.extend(self.drop_locals(&l)?);
        }
        if !found && !out.is_empty() {
            return unsup("jump out of a scope with destructors to an unknown target");
        }
        Ok(out)
    }

    /// The jump `j` (`break`/`continue` to `dest`, the expression `e`) after the drops of the
    /// scopes it leaves.
    fn jump_drops(&mut self, e: &'tcx hir::Expr<'tcx>, dest: hir::Destination, j: Tr) -> R<Tr> {
        let mut st = self.exit_drops(dest.target_id.ok())?;
        if st.is_empty() { return Ok(j) }
        st.push(j.s);
        Ok(self.jump_stmts(e, st))
    }

    /// The statements `st` ending with a jump (of the expression `e`): a block (of any type, as
    /// the jump), and, where it ends a block, the statements themselves (see `diverging`).
    fn jump_stmts(&mut self, e: &'tcx hir::Expr<'tcx>, st: Vec<String>) -> Tr {
        let st = st.join("\n");
        self.stmt_jumps.insert(e.hir_id, st.clone());
        Tr::block(format!("{{\n{}\n}}", st))
    }

    /// The local `hid` (just declared) owns its value: if dropping it runs a destructor (see
    /// `needs_glue`), it is dropped where its scope ends. When a use moves its value out, or it is
    /// not initialised (`init` false), a flag tells whether it holds one (returned: its
    /// declaration). A use moving a part with a destructor out, or a closure capturing it by value,
    /// is not supported.
    fn own(&mut self, hid: HirId, init: bool) -> R<Vec<String>> {
        let t = self.node_ty(hid);
        if !self.needs_glue(t) { return Ok(vec![]) }
        let l = self.locals.get(&hid).cloned().expect("an owned local is declared");
        // the uses of the local in the body (also in closures), collected once
        if self.local_uses.is_none() {
            let body = self.tcx.hir_body_owned_by(self.key.0.expect_local());
            let mut v = LocalUses { tcx: self.tcx, typeck: self.typeck, uses: HashMap::new(), by_value: HashSet::new() };
            v.visit_body(body);
            self.local_uses = Some((v.uses, v.by_value));
        }
        let (uses, by_value) = self.local_uses.as_ref().expect("collected");
        if by_value.contains(&hid) {
            return unsup("closure capturing a value with a destructor");
        }
        let uses = uses.get(&hid).cloned().unwrap_or_default();
        let mut moves = vec![];
        for u in uses {
            if self.use_kind(u)? == UseKind::Move {
                moves.push(u.hir_id);
            }
        }
        let mut out = vec![];
        let flag = if !init || !moves.is_empty() {
            let f = self.fresh(&format!("{}_live", l.name));
            let a = self.alloc(self.tcx.types.bool)?;
            out.push(self.let_binding(&f, hir::Mutability::Mut, &a, if init { "true" } else { "false" }));
            for m in moves {
                self.moved_uses.insert(m, f.clone());
            }
            self.local_flags.insert(hid, f.clone());
            Some(f)
        } else {
            None
        };
        let dl = DropLocal { name: l.name, cell: l.cell, ty: t, flag };
        match self.drop_scopes.last_mut() {
            Some(DropScope::Block(ls)) | Some(DropScope::Body(ls)) => ls.push(dl),
            _ => return unsup("local with a destructor outside a block"),
        }
        Ok(out)
    }

    /// How the use `p` (a path to a local with a destructor) treats the value; an error for a
    /// move of a part with a destructor out of it, or a value discarded by a statement.
    fn use_kind(&self, p: &'tcx hir::Expr<'tcx>) -> R<UseKind> {
        let parent = self.tcx.parent_hir_node(p.hir_id);
        let adj = self.typeck.expr_adjustments(p);
        if !adj.is_empty() {
            // borrowed (autoref): a place
            if adj.iter().any(|a| matches!(a.kind, Adjust::Borrow(_))) { return Ok(UseKind::Place) }
            // dereferenced (a `Box`): a field read through it is a place, see below; anything else
            // moves the contents out of the box
            if adj.iter().any(|a| matches!(a.kind, Adjust::Deref(_)))
                && !matches!(parent, hir::Node::Expr(par) if matches!(par.kind, ExprKind::Field(..)))
            {
                return unsup("move out of a box holding a value with a destructor");
            }
            // a coercion of the value (unsizing): moved
            if !adj.iter().any(|a| matches!(a.kind, Adjust::Deref(_))) { return Ok(UseKind::Move) }
        }
        let bad_bindings = |pat: &'tcx hir::Pat<'tcx>| {
            let mut bad = false;
            pat.walk_always(|q| {
                if let PatKind::Binding(hir::BindingMode(hir::ByRef::No, _), h, _, _) = q.kind
                    && self.needs_glue(self.node_ty(h))
                {
                    bad = true;
                }
            });
            bad
        };
        Ok(match self.tcx.parent_hir_node(p.hir_id) {
            hir::Node::Expr(par) => match par.kind {
                ExprKind::AddrOf(..) => UseKind::Place,
                // the operand of an overloaded `+=` or index taken by value is moved
                ExprKind::AssignOp(_, lhs, _) | ExprKind::Index(lhs, _, _) => {
                    if lhs.hir_id == p.hir_id { UseKind::Place } else { UseKind::Move }
                }
                // the contents of a `Box`: moved out if they have a destructor and the use moves them
                ExprKind::Unary(UnOp::Deref, _) => {
                    if self.needs_glue(self.ty_of(par)) && self.use_kind(par)? == UseKind::Move {
                        return unsup("move out of a box holding a value with a destructor");
                    }
                    UseKind::Place
                }
                // a part: moved out if it has a destructor and its use moves it
                ExprKind::Field(..) => {
                    if self.needs_glue(self.ty_of(par)) && self.use_kind(par)? == UseKind::Move {
                        return unsup("move of a part with a destructor out of a value");
                    }
                    UseKind::Place
                }
                // assigned (the old value is dropped there, see `expr`)
                ExprKind::Assign(lhs, _, _) if lhs.hir_id == p.hir_id => UseKind::Place,
                ExprKind::Match(s, arms, _) if s.hir_id == p.hir_id => {
                    if arms.iter().any(|a| bad_bindings(a.pat)) {
                        return unsup("move of a part with a destructor out of a value");
                    }
                    UseKind::Place
                }
                ExprKind::Let(le) if le.init.hir_id == p.hir_id => {
                    if bad_bindings(le.pat) {
                        return unsup("move of a part with a destructor out of a value");
                    }
                    UseKind::Place
                }
                ExprKind::Struct(_, _, hir::StructTailExpr::Base(b)) if b.hir_id == p.hir_id => {
                    return unsup("functional update of a value with a destructor");
                }
                _ => UseKind::Move,
            },
            hir::Node::LetStmt(l) => match l.pat.kind {
                PatKind::Wild | PatKind::Binding(hir::BindingMode(hir::ByRef::Yes(..), _), ..) => UseKind::Place,
                PatKind::Binding(..) => UseKind::Move,
                _ if bad_bindings(l.pat) => return unsup("move of a part with a destructor out of a value"),
                _ => UseKind::Place,
            },
            hir::Node::Stmt(_) => return unsup("value with a destructor discarded by a statement"),
            _ => UseKind::Move,
        })
    }
}

/// Whether `e` is a place expression (a local or a static, or a field, element or dereference of
/// one).
fn is_place_expr<'tcx>(typeck: &TypeckResults<'tcx>, e: &hir::Expr<'tcx>) -> bool {
    match e.kind {
        ExprKind::Path(ref qp) => matches!(typeck.qpath_res(qp, e.hir_id), Res::Local(_) | Res::Def(DefKind::Static { .. }, _)),
        // a part of a place (of a temporary it is a temporary)
        ExprKind::Field(b, _) | ExprKind::Index(b, _, _) => is_place_expr(typeck, b),
        // what a reference points to is a place; the contents of a `Box` are where the box is
        ExprKind::Unary(UnOp::Deref, b) => {
            matches!(typeck.expr_ty_adjusted(b).kind(), ty::Ref(..) | ty::RawPtr(..)) || is_place_expr(typeck, b)
        }
        _ => false,
    }
}

/// The paths to each local in a body (also in its closures), and the locals a closure captures
/// by value.
struct LocalUses<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    uses: HashMap<HirId, Vec<&'tcx hir::Expr<'tcx>>>,
    by_value: HashSet<HirId>,
}

impl<'tcx> Visitor<'tcx> for LocalUses<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx hir::Expr<'tcx>) {
        match e.kind {
            ExprKind::Path(ref qp) => {
                if let Res::Local(h) = self.typeck.qpath_res(qp, e.hir_id) {
                    self.uses.entry(h).or_default().push(e);
                }
            }
            ExprKind::Closure(c) => {
                for cap in self.typeck.closure_min_captures_flattened(c.def_id) {
                    if !matches!(cap.info.capture_kind, ty::UpvarCapture::ByRef(_)) {
                        self.by_value.insert(cap.get_root_variable());
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// Finds, in a closure body, a mutation of a place owned by a captured variable (the variable,
/// its fields, elements or boxed contents, not what a reference in it points to): an assignment
/// to it, or a mutable borrow of it (explicit, or an adjustment: autoref of a `&mut self` method
/// receiver, `IndexMut`, compound assignment, `DerefMut`).
struct CaptureMutation<'a, 'tcx> {
    typeck: &'tcx TypeckResults<'tcx>,
    captured: &'a HashSet<HirId>,
    found: bool,
}

impl<'a, 'tcx> CaptureMutation<'a, 'tcx> {
    /// The variable owning the place `e`, if `e` is a place of a captured variable.
    fn owner(&self, e: &hir::Expr<'tcx>) -> Option<HirId> {
        match e.kind {
            ExprKind::Path(ref qp) => match self.typeck.qpath_res(qp, e.hir_id) {
                Res::Local(h) if self.captured.contains(&h) => Some(h),
                _ => None,
            },
            ExprKind::Field(b, _) | ExprKind::Index(b, _, _) | ExprKind::DropTemps(b) => self.owner(b),
            ExprKind::Unary(UnOp::Deref, b) if self.typeck.expr_ty(b).is_box() => self.owner(b),
            _ => None,
        }
    }

    /// Do the adjustments of `e` borrow its place mutably (before going through a reference)?
    fn borrowed_mutably(&self, e: &hir::Expr<'tcx>) -> bool {
        let mut t = self.typeck.expr_ty(e);
        for adj in self.typeck.expr_adjustments(e) {
            match &adj.kind {
                Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut { .. })) => return true,
                Adjust::Deref(DerefAdjustKind::Overloaded(d)) => return d.mutbl.is_mut(),
                Adjust::Deref(_) if !t.is_box() => return false,
                _ => {}
            }
            t = adj.target;
        }
        false
    }
}

impl<'a, 'tcx> Visitor<'tcx> for CaptureMutation<'a, 'tcx> {
    fn visit_expr(&mut self, e: &'tcx hir::Expr<'tcx>) {
        let mutated = match e.kind {
            ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => self.owner(lhs).is_some(),
            ExprKind::AddrOf(_, hir::Mutability::Mut, x) => self.owner(x).is_some(),
            _ => false,
        };
        if mutated || (self.owner(e).is_some() && self.borrowed_mutably(e)) {
            self.found = true;
        }
        intravisit::walk_expr(self, e);
    }
}

/// The flags of `fmt::FormattingOptions::new()`: fill `' '`, alignment unknown.
const FMT_DEFAULT_FLAGS: u32 = ' ' as u32 | (3 << 29);

/// A `format_args!` expansion (see `BodyTr::fmt_args`): the values formatted (each evaluated
/// once, in order), the `rt::Argument`s (constructor, index of the value) and the template.
struct FmtArgs<'tcx> {
    vals: Vec<&'tcx hir::Expr<'tcx>>,
    args: Vec<(DefId, usize)>,
    parts: Vec<FmtPart>,
}

/// A part of a `fmt::Arguments` template (see `core::fmt::Arguments`).
enum FmtPart {
    Lit(String),
    /// a placeholder: its options, the `rt::Argument`s giving a dynamic width or precision, and
    /// the `rt::Argument` formatted (`None`: the next one)
    Ph { flags: u32, width: u16, precision: u16, width_arg: Option<usize>, precision_arg: Option<usize>, arg: Option<usize> },
}

/// Decode a `fmt::Arguments` template (the byte encoding of `core::fmt::Arguments`, read as
/// `core::fmt::write` reads it).
fn decode_fmt_template(b: &[u8]) -> Option<Vec<FmtPart>> {
    let mut parts = vec![];
    let mut i = 0usize;
    let u16_at = |i: usize| -> Option<u16> { Some(u16::from_le_bytes([*b.get(i)?, *b.get(i + 1)?])) };
    loop {
        let n = *b.get(i)?;
        i += 1;
        if n == 0 {
            return Some(parts);
        } else if n < 0x80 {
            parts.push(FmtPart::Lit(std::str::from_utf8(b.get(i..i + n as usize)?).ok()?.to_string()));
            i += n as usize;
        } else if n == 0x80 {
            let len = u16_at(i)? as usize;
            i += 2;
            parts.push(FmtPart::Lit(std::str::from_utf8(b.get(i..i + len)?).ok()?.to_string()));
            i += len;
        } else if n == 0xC0 {
            parts.push(FmtPart::Ph { flags: FMT_DEFAULT_FLAGS, width: 0, precision: 0, width_arg: None, precision_arg: None, arg: None });
        } else if n > 0xC0 {
            let mut flags = FMT_DEFAULT_FLAGS;
            let (mut width, mut precision, mut arg) = (0u16, 0u16, None);
            if n & 1 != 0 {
                flags = u32::from_le_bytes([*b.get(i)?, *b.get(i + 1)?, *b.get(i + 2)?, *b.get(i + 3)?]);
                i += 4;
            }
            if n & 2 != 0 {
                width = u16_at(i)?;
                i += 2;
            }
            if n & 4 != 0 {
                precision = u16_at(i)?;
                i += 2;
            }
            if n & 8 != 0 {
                arg = Some(u16_at(i)? as usize);
                i += 2;
            }
            let width_arg = (n & 16 != 0).then_some(width as usize);
            let precision_arg = (n & 32 != 0).then_some(precision as usize);
            parts.push(FmtPart::Ph { flags, width, precision, width_arg, precision_arg, arg });
        } else {
            return None;
        }
    }
}

/// A conversion between a `Vec` and a list (see `Body::vec_conversion`).
enum VecConversion {
    /// the elements of the `Vec`
    Elems,
    /// a `Vec` whose capacity is the number of the elements, with the given layout
    FromList(Tr),
    /// a `Vec` of the elements in a new allocation, with the given layout
    Alloc(Tr),
    /// a clone of the `Vec`
    Clone,
}

/// The standard library functions with a uRust counterpart (see `std_call`).
#[derive(Clone, Copy, PartialEq)]
enum StdFn {
    Clone,
    Eq,
    Ne,
    Cmp,
    OptionUnwrap,
    OptionExpect,
    OptionIsSome,
    OptionIsNone,
    OptionOkOr,
    OptionTake,
    ResultUnwrap,
    ResultExpect,
    ResultIsOk,
    ResultIsErr,
    ResultOk,
    ResultUnwrapOr,
    Len,
    /// `Vec::new`, `Vec::with_capacity` (AutoCorrode's `StdLib_Vec`, with the elements' layout)
    VecNew,
    VecWithCapacity,
    /// `String::new`, `String::with_capacity`: the empty byte list
    StringNew,
    /// a `Vec` of the elements of a boxed slice (`into_vec`, the expansion of `vec![..]`), whose
    /// capacity is their number
    VecFromList,
    /// a `Vec` of the elements of a list in a new allocation (`to_vec`, `String::into_bytes`)
    VecAlloc,
    /// the elements of a `Vec` (`into_boxed_slice`, `String::from_utf8_unchecked`)
    VecElems,
    /// `String::from_utf8` of a `Vec<u8>`
    StringFromUtf8,
    /// `FromUtf8Error::into_bytes`: the `Vec<u8>`
    FromUtf8ErrorIntoBytes,
    BoxNew,
    Drop,
    RangeInclusiveNew,
    /// `ToOwned::to_owned`, `From::from`, `Into::into`, `as_slice`, ...: the identity when the
    /// argument and the result have the same HOL type
    Conversion,
    SliceIter,
    SliceIterMut,
    VecFromElem,
    SliceSwap,
    /// an operation of integers, by its AutoCorrode name
    IntOp(&'static str),
    /// a method of `fmt::Formatter`, by the name of its model
    FmtMethod(&'static str),
    /// the `fmt` method of a formatting trait (`Display`, `Debug`, `LowerHex`, ...)
    FmtTrait(DefId),
    /// a model of AutoCorrode's `StdLib_Frontend_Models` applied to the arguments
    Model(&'static str),
    /// as `Model`, with the HOL type of the result stated (the arguments do not determine it)
    ModelTyped(&'static str),
    /// `<[T]>::get` with an index or a range
    SliceGet,
    /// `<[T]>::copy_within` with a `Range` or `RangeInclusive`
    SliceCopyWithin,
    /// `TryInto::try_into`, `TryFrom::try_from` from a slice to an array
    TryIntoArray,
    /// a method of `HashMap` taking a key (by its model's name), for keys with structural equality
    HashMapKey(&'static str),
    /// `<[T]>::sort` by the `Ord` of the elements
    SliceSort,
    /// `Vec::dedup` with structural equality
    VecDedup,
    /// `PartialOrd::partial_cmp` on unsigned integers
    PartialCmp,
    /// `Default::default` of a standard type, or derived
    DefaultFn,
    /// `char::encode_utf8`
    CharEncodeUtf8,
    /// `intrinsics::discriminant_value` of a local enum
    DiscriminantValue,
    /// `Range(Inclusive)::contains`
    RangeContains,
    /// `<[T]>::get_mut` with an index
    SliceGetMut,
    /// `ToString::to_string`
    ToString,
    /// a method of `str` taking a pattern (`starts_with`, `find`, ...), by the common prefix of the
    /// names of its models for a `char` and for a string pattern
    StrPattern(&'static str),
    /// an ASCII class test of `u8` or `char` (`is_ascii_digit`, ...), by the HOL predicate on the code
    AsciiTest(&'static str),
    /// `str::get` with a range
    StrGet,
    /// `Add::add`, `AddAssign::add_assign` (on a `String`)
    StringAdd,
    StringAddAssign,
    /// `str::parse` into an integer type
    StrParse,
    /// `Ord::min`, `cmp::min` (and `max`) on unsigned integers
    OrdMin,
    OrdMax,
    /// `mem::size_of`
    SizeOf,
    /// a method of `Iterator`
    Iter(IterFn),
}

/// The methods of `Iterator` with models (see `iter_call`).
#[derive(Clone, Copy, PartialEq)]
enum IterFn {
    Next,
    Enumerate,
    Zip,
    Skip,
    Take,
    TakeWhile,
    Map,
    /// `rev`, `copied`, `cloned`: the state of the inner iterator
    Same,
    Count,
    Collect,
    Filter,
    Any,
    Min,
    ForEach,
}

/// A lang item, or a diagnostic item by its name in the table of the standard library.
enum Item {
    Lang(LangItem),
    Diag(&'static str),
}

/// The functions of `StdFn` that have their own lang or diagnostic item.
const STD_ITEMS: &[(Item, StdFn)] = &[
    (Item::Lang(LangItem::CloneFn), StdFn::Clone),
    (Item::Diag("cmp_partialeq_eq"), StdFn::Eq),
    (Item::Diag("cmp_partialeq_ne"), StdFn::Ne),
    (Item::Diag("ord_cmp_method"), StdFn::Cmp),
    (Item::Diag("option_unwrap"), StdFn::OptionUnwrap),
    (Item::Diag("option_expect"), StdFn::OptionExpect),
    (Item::Diag("result_ok_method"), StdFn::ResultOk),
    (Item::Diag("vec_new"), StdFn::VecNew),
    (Item::Diag("vec_with_capacity"), StdFn::VecWithCapacity),
    (Item::Diag("box_new"), StdFn::BoxNew),
    (Item::Diag("mem_drop"), StdFn::Drop),
    (Item::Lang(LangItem::RangeInclusiveNew), StdFn::RangeInclusiveNew),
    (Item::Diag("to_string_method"), StdFn::ToString),
    (Item::Diag("to_owned_method"), StdFn::Conversion),
    (Item::Lang(LangItem::FromFn), StdFn::Conversion),
    (Item::Diag("vec_as_slice"), StdFn::VecElems),
    (Item::Diag("string_as_str"), StdFn::Conversion),
    (Item::Diag("slice_iter"), StdFn::SliceIter),
    (Item::Diag("vec_from_elem"), StdFn::VecFromElem),
    (Item::Diag("cmp_min"), StdFn::OrdMin),
    (Item::Diag("cmp_ord_min"), StdFn::OrdMin),
    (Item::Diag("cmp_max"), StdFn::OrdMax),
    (Item::Diag("cmp_ord_max"), StdFn::OrdMax),
    (Item::Diag("mem_size_of"), StdFn::SizeOf),
    (Item::Diag("try_from_fn"), StdFn::TryIntoArray),
    (Item::Diag("cmp_partialord_cmp"), StdFn::PartialCmp),
    (Item::Diag("mem_swap"), StdFn::Model("mem_swap")),
    (Item::Diag("mem_replace"), StdFn::Model("mem_replace")),
    (Item::Diag("default_fn"), StdFn::DefaultFn),
    (Item::Diag("str_from_utf8"), StdFn::Model("str_from_utf8")),
    (Item::Diag("str_from_utf8_unchecked"), StdFn::Conversion),
];

/// `if c1 { b1 } else { if c2 { b2 } else { .. } }` for (condition, body) branches;
/// `None` is an unconditional branch.
fn if_chain(branches: Vec<(Option<String>, String)>) -> String {
    let mut acc: Option<String> = None;
    for (cond, body) in branches.into_iter().rev() {
        acc = Some(match (cond, acc) {
            (None, _) => body,
            (Some(c), None) => format!("if {} {{\n{}\n}} else {{\n panic!(\"non-exhaustive match\")\n}}", c, body),
            (Some(c), Some(rest)) => format!("if {} {{\n{}\n}} else {{\n{}\n}}", c, body, rest),
        });
    }
    acc.unwrap_or_else(|| "panic!(\"empty match\")".into())
}

/// The statements `pro` followed by `body`.
fn with_prologue(pro: &[String], body: &str) -> String {
    let mut s = pro.join("\n");
    if !s.is_empty() {
        s.push('\n');
    }
    s.push_str(body);
    s
}

fn paren_if(c: &str) -> String {
    if c.contains(' ') { format!("({})", c) } else { c.to_string() }
}

fn contains_let(e: &hir::Expr<'_>) -> bool {
    match e.kind {
        ExprKind::Let(_) => true,
        ExprKind::Binary(_, l, r) => contains_let(l) || contains_let(r),
        ExprKind::DropTemps(x) => contains_let(x),
        _ => false,
    }
}

/// The HOL term of a string literal (`str` is the list of its UTF-8 bytes, see `Frontend::ty`):
/// the concatenation of the runs of characters printable in `STR ''…''`, as `str_lit (STR ''…'')`
/// (their ASCII bytes), and of the encodings `char_utf8 c` of the other characters.
fn hol_str(s: &str) -> String {
    let mut pieces = vec![];
    let mut run = String::new();
    for c in s.chars() {
        if names::hol_string_ok(&c.to_string()) {
            run.push(c);
        } else {
            if !run.is_empty() { pieces.push(format!("str_lit (STR ''{}'')", std::mem::take(&mut run))) }
            pieces.push(format!("char_utf8 0x{:X}", c as u32));
        }
    }
    if !run.is_empty() || pieces.is_empty() { pieces.push(format!("str_lit (STR ''{}'')", run)) }
    pieces.join(" @ ")
}

/// The HOL term of a character literal (`char` is its code point, a `32 word`): a printable ASCII
/// character as `char_code CHR ''c''`, another as its code point.
fn hol_char(c: char) -> String {
    if c.is_ascii_alphanumeric() || " !#$%&()*+,-./:;<=>?@[]^_`{|}~".contains(c) {
        format!("char_code CHR ''{}''", c)
    } else {
        format!("(0x{:X} :: 32 word)", c as u32)
    }
}

/// Expand a pattern list with a `..` at position `ddpos` to `n` entries.
fn expand_dotdot<'h>(ps: &'h [hir::Pat<'h>], ddpos: hir::DotDotPos, n: usize) -> Vec<Option<&'h hir::Pat<'h>>> {
    match ddpos.as_opt_usize() {
        None => ps.iter().map(Some).collect(),
        Some(k) => {
            let mut v: Vec<Option<&hir::Pat<'_>>> = ps[..k].iter().map(Some).collect();
            for _ in 0..(n - ps.len()) { v.push(None); }
            v.extend(ps[k..].iter().map(Some));
            v
        }
    }
}

/// Join statement strings. Entries starting with `\u{3}` are tail expressions,
/// entries starting with `\u{4}` end with their own semicolon (return/break/continue).
fn join_seq(parts: Vec<String>) -> String {
    let mut out = String::new();
    let n = parts.len();
    for (i, p) in parts.into_iter().enumerate() {
        let last = i + 1 == n;
        if let Some(t) = p.strip_prefix('\u{3}') {
            out.push_str(t);
        } else {
            // statements already carry a trailing ';'
            out.push_str(p.strip_prefix('\u{4}').unwrap_or(&p));
            if !last { out.push('\n'); }
        }
    }
    out
}
