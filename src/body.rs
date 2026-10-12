//! Translation of HIR bodies (expressions, statements, patterns) to uRust text.
//!
//! Memory model:
//! * a `let mut` local (or a `mut` parameter / pattern binding) becomes a uRust
//!   mutable local, i.e. a reference allocated with `let mut`; reading it is `*x`;
//! * a value of type `&mut T` is a reference `('addr,'gv,T) Global_Store.ref`;
//! * a value of type `&T` is represented by the value of type `T` (shared
//!   borrows of data without interior mutability are observationally values).

use std::collections::{BTreeSet, HashMap};

use rustc_ast::ast::{LitIntType, LitKind};
use rustc_hir as hir;
use rustc_hir::def::{CtorKind, CtorOf, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{BinOpKind, ExprKind, HirId, LoopSource, MatchSource, PatKind, StmtKind, UnOp};
use rustc_middle::ty::adjustment::{Adjust, AutoBorrow, AutoBorrowMutability, DerefAdjustKind, PointerCoercion};
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TypeckResults};
use rustc_span::Span;

use crate::frontend::{Frontend, paren_ty};
use crate::names;

pub struct Unsup(pub String);
pub type R<T> = Result<T, Unsup>;

fn unsup<T>(msg: impl Into<String>) -> R<T> {
    Err(Unsup(msg.into()))
}

/// A translated expression with its uRust precedence (1000 = atomic).
#[derive(Clone, Debug)]
pub struct Tr {
    pub s: String,
    pub prec: u32,
}

impl Tr {
    pub fn atom(s: impl Into<String>) -> Tr { Tr { s: s.into(), prec: 1000 } }
    pub fn new(s: impl Into<String>, prec: u32) -> Tr { Tr { s: s.into(), prec } }
    /// Render with at least precedence `p`, adding parentheses otherwise.
    pub fn at(&self, p: u32) -> String {
        if self.prec >= p { self.s.clone() } else { format!("({})", self.s) }
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

/// Information about a pattern translation for a uRust `match`/`if let`.
struct PatTr {
    pat: String,
    /// Extra guard conditions (from literal / range sub-patterns).
    conds: Vec<String>,
    /// Statements to run at the start of the arm (mutable bindings).
    prologue: Vec<String>,
}

pub struct BodyTr<'a, 'tcx> {
    pub fe: &'a mut Frontend<'tcx>,
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    owner: LocalDefId,
    locals: HashMap<HirId, Local>,
    fresh: usize,
    pub calls: crate::frontend::DefSet,
    pub comments: Vec<String>,
}

const FUEL: &str = "#[fuel(\\<epsilon>\\<open>urust_fuel\\<close>)]";

impl<'a, 'tcx> BodyTr<'a, 'tcx> {
    pub fn new(fe: &'a mut Frontend<'tcx>, owner: LocalDefId) -> Self {
        let tcx = fe.tcx;
        let typeck = tcx.typeck(owner);
        BodyTr { fe, tcx, typeck, owner, locals: HashMap::new(), fresh: 0, calls: crate::frontend::DefSet::default(), comments: vec![] }
    }

    fn fresh(&mut self, base: &str) -> String {
        self.fresh += 1;
        format!("{}_{}", base, self.fresh)
    }

    fn placeholder(&mut self, msg: &str, sp: Span) -> Tr {
        self.fe.note_placeholder(msg, sp);
        let snip = crate::frontend::one_line(&self.fe.snippet(sp));
        Tr::new(
            format!("unimplemented!(\"{}\")", names::string_token(&format!("UNSUPPORTED {}: {}", msg, snip))),
            999,
        )
    }

    fn ty_of(&self, e: &hir::Expr<'tcx>) -> Ty<'tcx> { self.typeck.expr_ty(e) }
    fn ty_adj(&self, e: &hir::Expr<'tcx>) -> Ty<'tcx> { self.typeck.expr_ty_adjusted(e) }

    fn peel_refs(t: Ty<'tcx>) -> Ty<'tcx> {
        let mut t = t;
        while let ty::Ref(_, inner, _) = t.kind() { t = *inner; }
        t
    }

    fn is_unit_like(t: Ty<'tcx>) -> bool { t.is_unit() || t.is_never() }

    // ------------------------------------------------------------------
    // Function bodies
    // ------------------------------------------------------------------

    /// Translate the body of a function; returns (param names, body text).
    pub fn fn_body(&mut self, body: &'tcx hir::Body<'tcx>) -> R<(Vec<String>, String)> {
        let mut params = vec![];
        let mut prologue = vec![];
        for (i, p) in body.params.iter().enumerate() {
            match p.pat.kind {
                PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, None) => {
                    let n = names::local_name(ident.as_str());
                    let n = if params.contains(&n) { format!("{}_{}", n, i) } else { n };
                    params.push(n.clone());
                    if m.is_mut() {
                        let t = self.typeck.node_type(hid);
                        self.alloc(t, p.pat.span)?;
                        prologue.push(format!("let mut {} = {};", n, n));
                        self.locals.insert(hid, Local { name: n, cell: true });
                    } else {
                        self.locals.insert(hid, Local { name: n, cell: false });
                    }
                }
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
        let mut s = prologue.join("\n");
        if !s.is_empty() { s.push('\n'); }
        s.push_str(&b);
        Ok((params, s))
    }

    /// Translate an expression used as a whole body (no braces).
    fn block_expr_inner(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<String> {
        match e.kind {
            ExprKind::Block(b, None) if self.typeck.expr_adjustments(e).is_empty() => self.block_seq(b.stmts, b.expr),
            _ => {
                let t = self.expr(e);
                Ok(t.s)
            }
        }
    }

    fn alloc(&mut self, t: Ty<'tcx>, sp: Span) -> R<()> {
        let h = self.fe.ty(t);
        if h.contains("'r") {
            let _ = sp;
            return unsup("mutable local of a generic type (needs a locale prism for a type parameter)");
        }
        self.fe.need_alloc(&h);
        Ok(())
    }

    // ------------------------------------------------------------------
    // Blocks and statements
    // ------------------------------------------------------------------

    fn block_seq(&mut self, stmts: &'tcx [hir::Stmt<'tcx>], tail: Option<&'tcx hir::Expr<'tcx>>) -> R<String> {
        let mut parts: Vec<String> = vec![];
        let mut ended_by_divergence = false;
        let mut i = 0;
        while i < stmts.len() {
            let st = &stmts[i];
            match st.kind {
                StmtKind::Item(_) => {}
                StmtKind::Let(l) => {
                    let (pre, post) = self.let_stmt(l)?;
                    let rest = self.block_seq(&stmts[i + 1..], tail)?;
                    let rest = if rest.trim().is_empty() { "()".to_string() } else { rest };
                    parts.push(format!("{}\n{}{}", pre, rest, post));
                    return Ok(join_seq(parts, true));
                }
                StmtKind::Expr(e) | StmtKind::Semi(e) => {
                    let t = self.ty_of(e);
                    let s = self.stmt_expr(e);
                    parts.push(s);
                    if t.is_never() {
                        ended_by_divergence = true;
                        break;
                    }
                }
            }
            i += 1;
        }
        if !ended_by_divergence {
            if let Some(t) = tail {
                let tt = self.expr(t);
                parts.push(format!("\u{3}{}", tt.s)); // \u{3} marks a tail expression
            }
        }
        Ok(join_seq(parts, false))
    }

    /// An expression in statement position, rendered as a complete statement.
    fn stmt_expr(&mut self, e: &'tcx hir::Expr<'tcx>) -> String {
        let t = self.ty_of(e);
        match e.kind {
            ExprKind::Ret(_) | ExprKind::Break(..) | ExprKind::Continue(_) => {
                let tr = self.expr(e);
                if tr.s.ends_with(';') { return format!("\u{4}{}", tr.s) } // \u{4}: ends with own semicolon
                return format!("{};", tr.s);
            }
            _ => {}
        }
        let tr = self.expr(e);
        if Self::is_unit_like(t) || tr.s.starts_with("unimplemented!") {
            format!("{};", tr.at(11))
        } else {
            format!("let _ = {};", tr.at(20))
        }
    }

    /// A `let` statement as (prefix, suffix): the rest of the block goes in between.
    fn let_stmt(&mut self, l: &'tcx hir::LetStmt<'tcx>) -> R<(String, String)> {
        if let Some(els) = l.els {
            let init = l.init.ok_or(Unsup("let-else without initializer".into()))?;
            let iv = self.expr(init);
            let p = self.pat(l.pat)?;
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
                    let t = self.typeck.node_type(hid);
                    self.alloc(t, l.pat.span)?;
                    let ht = self.fe.ty(t);
                    self.locals.insert(hid, Local { name: n.clone(), cell: true });
                    Ok((format!("let mut {} = \\<llangle>undefined :: {}\\<rrangle>;", n, ht), String::new()))
                } else {
                    unsup("let without initializer and with a non-identifier pattern")
                }
            }
            Some(init) => {
                let iv = self.expr(init);
                Ok((self.bind_pattern(l.pat, iv)?, String::new()))
            }
        }
    }

    /// `let <pat> = <value>;` for an irrefutable pattern (one or more statements).
    fn bind_pattern(&mut self, pat: &'tcx hir::Pat<'tcx>, v: Tr) -> R<String> {
        match pat.kind {
            PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, None) => {
                let n = names::local_name(ident.as_str());
                if m.is_mut() {
                    let t = self.typeck.node_type(hid);
                    self.alloc(t, pat.span)?;
                    self.locals.insert(hid, Local { name: n.clone(), cell: true });
                    Ok(format!("let mut {} = {};", n, v.at(20)))
                } else {
                    self.locals.insert(hid, Local { name: n.clone(), cell: false });
                    Ok(format!("let {} = {};", n, v.at(20)))
                }
            }
            PatKind::Wild => Ok(format!("let _ = {};", v.at(20))),
            _ => {
                let tmp = self.fresh("destr");
                let lets = self.irrefutable(pat, &Tr::atom(tmp.clone()))?;
                Ok(format!("let {} = {};\n{}", tmp, v.at(20), lets.join("\n")))
            }
        }
    }

    /// Destructure an irrefutable pattern by projections. Returns `let` statements.
    fn irrefutable(&mut self, pat: &'tcx hir::Pat<'tcx>, v: &Tr) -> R<Vec<String>> {
        let mut out = vec![];
        match pat.kind {
            PatKind::Wild => {}
            PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, sub) => {
                let n = names::local_name(ident.as_str());
                if m.is_mut() {
                    let t = self.typeck.node_type(hid);
                    self.alloc(t, pat.span)?;
                    out.push(format!("let mut {} = {};", n, v.at(20)));
                    self.locals.insert(hid, Local { name: n.clone(), cell: true });
                } else {
                    out.push(format!("let {} = {};", n, v.at(20)));
                    self.locals.insert(hid, Local { name: n.clone(), cell: false });
                }
                if let Some(s) = sub {
                    out.extend(self.irrefutable(s, &Tr::atom(n))?);
                }
            }
            PatKind::Binding(..) => return unsup("`ref` binding"),
            PatKind::Tuple(ps, ddpos) => {
                let t = Self::peel_refs(self.typeck.pat_ty(pat));
                let n = match t.kind() { ty::Tuple(ts) => ts.len(), _ => ps.len() };
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    if let Some(p) = p {
                        if n > 16 { return unsup("tuple with more than 16 components") }
                        let proj = Tr::new(format!("{}.{}", v.at(998), k), 998);
                        out.extend(self.irrefutable(p, &proj)?);
                    }
                }
            }
            PatKind::Struct(_, fields, _) => {
                let t = Self::peel_refs(self.typeck.pat_ty(pat));
                let ty::Adt(def, _) = t.kind() else { return unsup("struct pattern on non-ADT") };
                if !def.is_struct() || !def.did().is_local() { return unsup("refutable struct pattern in irrefutable position") }
                let adt = def.did();
                for f in fields.iter() {
                    let fidx = self.typeck.field_index(f.hir_id).as_usize();
                    let proj = self.field_read(adt, fidx, v)?;
                    out.extend(self.irrefutable(f.pat, &proj)?);
                }
            }
            PatKind::TupleStruct(_, ps, ddpos) => {
                let t = Self::peel_refs(self.typeck.pat_ty(pat));
                let ty::Adt(def, _) = t.kind() else { return unsup("tuple-struct pattern on non-ADT") };
                if !def.is_struct() || !def.did().is_local() { return unsup("refutable tuple-struct pattern in irrefutable position") }
                let adt = def.did();
                let n = def.non_enum_variant().fields.len();
                for (k, p) in expand_dotdot(ps, ddpos, n).into_iter().enumerate() {
                    if let Some(p) = p {
                        let proj = self.field_read(adt, k, v)?;
                        out.extend(self.irrefutable(p, &proj)?);
                    }
                }
            }
            PatKind::Ref(p, _, _) | PatKind::Deref(p) => out.extend(self.irrefutable(p, v)?),
            _ => return unsup("pattern in irrefutable position"),
        }
        Ok(out)
    }

    /// Read field `fidx` of a value of local struct `adt`.
    fn field_read(&mut self, adt: DefId, fidx: usize, v: &Tr) -> R<Tr> {
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
    pub fn expr(&mut self, e: &'tcx hir::Expr<'tcx>) -> Tr {
        match self.pv_adjusted(e) {
            Ok(pv) => self.to_val(pv),
            Err(Unsup(m)) => self.placeholder(&m, e.span),
        }
    }

    fn val(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let pv = self.pv_adjusted(e)?;
        Ok(self.to_val(pv))
    }

    fn to_val(&self, pv: PV) -> Tr {
        match pv {
            PV::Val(t) => t,
            PV::Ref(r) => Tr::new(format!("*{}", r.at(200)), 100),
        }
    }

    fn pv_adjusted(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<PV> {
        let mut pv = self.pv_unadj(e)?;
        let mut cur = self.ty_of(e);
        for adj in self.typeck.expr_adjustments(e) {
            pv = match &adj.kind {
                Adjust::NeverToAny => pv,
                Adjust::Deref(DerefAdjustKind::Builtin) => self.deref_pv(pv, cur)?,
                Adjust::Deref(DerefAdjustKind::Overloaded(_)) => {
                    // Box<T> ~ T, Vec<T> ~ [T] ~ list, String ~ str ~ String.literal
                    let a = self.fe.ty(Self::peel_refs(cur));
                    let b = self.fe.ty(Self::peel_refs(adj.target));
                    if a != b { return unsup(format!("overloaded dereference of `{}`", cur)) }
                    pv
                }
                Adjust::Deref(_) => return unsup("pinned dereference"),
                Adjust::Borrow(AutoBorrow::Ref(m)) => match m {
                    AutoBorrowMutability::Mut { .. } => self.borrow_mut(pv)?,
                    AutoBorrowMutability::Not => PV::Val(self.to_val(pv)),
                },
                Adjust::Borrow(_) => return unsup("raw or pinned auto-borrow"),
                Adjust::Pointer(PointerCoercion::Unsize) => pv,
                Adjust::Pointer(_) => return unsup("pointer coercion"),
                Adjust::GenericReborrow(_) => pv,
            };
            cur = adj.target;
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

    fn borrow_mut(&mut self, pv: PV) -> R<PV> {
        match pv {
            PV::Ref(r) => Ok(PV::Val(r)),
            PV::Val(_) => unsup("mutable borrow of a temporary value"),
        }
    }

    fn pv_unadj(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<PV> {
        match e.kind {
            ExprKind::Path(ref qp) => {
                if let Res::Local(hid) = self.typeck.qpath_res(qp, e.hir_id) {
                    let Some(l) = self.locals.get(&hid).cloned() else {
                        return unsup("use of a captured or unknown local");
                    };
                    return Ok(if l.cell { PV::Ref(Tr::atom(l.name)) } else { PV::Val(Tr::atom(l.name)) });
                }
                Ok(PV::Val(self.val_unadj(e)?))
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                if self.typeck.type_dependent_def_id(e.hir_id).is_some() {
                    let a = self.fe.ty(Self::peel_refs(self.ty_adj(inner)));
                    let b = self.fe.ty(self.ty_of(e));
                    if a == b { return self.pv_adjusted(inner) }
                    return unsup("overloaded dereference");
                }
                let t = self.ty_adj(inner);
                let p = self.pv_adjusted(inner)?;
                self.deref_pv(p, t)
            }
            ExprKind::Field(base, ident) => {
                let bpv = self.pv_adjusted(base)?;
                let bt = self.ty_adj(base);
                match bt.kind() {
                    ty::Adt(def, _) if def.is_struct() && def.did().is_local() => {
                        let fidx = self.typeck.field_index(e.hir_id).as_usize();
                        let adt = def.did();
                        let f = self.fe.field_name(adt, 0, fidx);
                        if !self.fe.record_adts.contains(&adt) {
                            return match bpv {
                                PV::Val(v) => Ok(PV::Val(self.field_read(adt, fidx, &v)?)),
                                PV::Ref(_) => unsup("field of a recursive struct through a reference"),
                            };
                        }
                        match bpv {
                            PV::Val(v) => Ok(PV::Val(Tr::new(format!("{}.{}", v.at(99), f), 100))),
                            PV::Ref(r) => Ok(PV::Ref(Tr::new(format!("{}.{}", r.at(99), f), 100))),
                        }
                    }
                    ty::Tuple(ts) => {
                        let k: usize = ident.as_str().parse().map_err(|_| Unsup("tuple field".into()))?;
                        if ts.len() > 16 { return unsup("tuple with more than 16 components") }
                        match bpv {
                            PV::Val(v) => Ok(PV::Val(Tr::new(format!("{}.{}", v.at(998), k), 998))),
                            PV::Ref(_) => unsup("tuple field through a reference / of a mutable local"),
                        }
                    }
                    _ => unsup(format!("field access on `{}`", bt)),
                }
            }
            ExprKind::Index(base, idx, _) => {
                let bt = Self::peel_refs(self.ty_adj(base));
                let list_like = match bt.kind() {
                    ty::Slice(_) | ty::Array(..) => true,
                    ty::Adt(def, _) => self.fe.std_adt(def.did()) == Some("Vec"),
                    _ => false,
                };
                if !list_like { return unsup(format!("indexing into `{}`", bt)) }
                let is_range = matches!(Self::peel_refs(self.ty_adj(idx)).kind(), ty::Adt(..));
                let mut bpv = self.pv_adjusted(base)?;
                // overloaded `Index(Mut)` auto-borrows the base: go back to the place
                let mut bt_adj = self.ty_adj(base);
                while let ty::Ref(_, inner, _) = bt_adj.kind() {
                    bpv = self.deref_pv(bpv, bt_adj)?;
                    bt_adj = *inner;
                }
                let i = self.val(idx)?;
                match bpv {
                    PV::Val(v) => Ok(PV::Val(Tr::new(format!("{}[{}]", v.at(100), i.s), 100))),
                    PV::Ref(r) if !is_range => Ok(PV::Ref(Tr::new(format!("{}[{}]", r.at(100), i.s), 100))),
                    PV::Ref(r) => Ok(PV::Val(Tr::new(format!("(*{})[{}]", r.at(200), i.s), 100))),
                }
            }
            _ => Ok(PV::Val(self.val_unadj(e)?)),
        }
    }

    /// The place denoted by an expression; must be a reference.
    fn place(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
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
        let tcx = self.tcx;
        match e.kind {
            ExprKind::Lit(lit) => self.lit(&lit.node, self.ty_of(e), false),
            ExprKind::Path(ref qp) => self.path_value(qp, e),
            ExprKind::Call(callee, args) => self.call_expr(e, callee, args),
            ExprKind::MethodCall(_, recv, args, _) => {
                let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else {
                    return unsup("unresolved method call");
                };
                let gargs = self.typeck.node_args(e.hir_id);
                let mut argv = vec![self.val(recv)?];
                for a in args.iter() { argv.push(self.val(a)?); }
                let mut arg_exprs = vec![recv];
                arg_exprs.extend(args.iter());
                self.call_def(did, gargs, argv, &arg_exprs, e)
            }
            ExprKind::Tup(es) => {
                if es.is_empty() { return Ok(Tr::atom("()")) }
                if es.len() == 1 { return unsup("1-tuple") }
                let v: R<Vec<String>> = es.iter().map(|x| self.val(x).map(|t| t.s)).collect();
                Ok(Tr::new(format!("({})", v?.join(", ")), 998))
            }
            ExprKind::Binary(op, l, r) => self.binary(e, op.node, l, r),
            ExprKind::Unary(UnOp::Not, x) => {
                let xt = Self::peel_refs(self.ty_adj(x));
                if !(xt.is_bool() || xt.is_integral()) { return self.overloaded_op(e, &[x]) }
                let v = self.val(x)?;
                Ok(Tr::new(format!("!{}", v.at(300)), 300))
            }
            ExprKind::Unary(UnOp::Neg, x) => {
                let xt = Self::peel_refs(self.ty_adj(x));
                if !xt.is_signed() { return self.overloaded_op(e, &[x]) }
                if let ExprKind::Lit(lit) = x.kind {
                    return self.lit(&lit.node, xt, true);
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
                MatchSource::ForLoopDesugar => self.for_loop(e, scrut, arms),
                MatchSource::TryDesugar(_) => {
                    let ExprKind::Call(_, [inner]) = scrut.kind else { return unsup("`?` desugaring") };
                    let v = self.val(inner)?;
                    Ok(Tr::new(format!("{}?", v.at(400)), 400))
                }
                MatchSource::Normal | MatchSource::Postfix => self.match_expr(scrut, arms),
                _ => unsup("async/await or format_args"),
            },
            ExprKind::Closure(c) => self.closure(e, c),
            ExprKind::Block(b, label) => {
                if label.is_some() { return unsup("labeled block") }
                let s = self.block_seq(b.stmts, b.expr)?;
                Ok(Tr::atom(format!("{{\n{}\n}}", s)))
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let p = self.place(lhs)?;
                let v = self.val(rhs)?;
                Ok(Tr::new(format!("*{} = {}", p.at(200), v.at(40)), 40))
            }
            ExprKind::AssignOp(op, lhs, rhs) => self.assign_op(e, op.node, lhs, rhs),
            ExprKind::Field(..) | ExprKind::Index(..) => {
                let pv = self.pv_unadj(e)?;
                Ok(self.to_val(pv))
            }
            ExprKind::AddrOf(hir::BorrowKind::Ref, m, x) => {
                if m.is_mut() {
                    let p = self.place(x)?;
                    Ok(p)
                } else {
                    self.val(x)
                }
            }
            ExprKind::AddrOf(..) => unsup("raw borrow"),
            ExprKind::Break(dest, val) => {
                if val.is_some() { return unsup("`break` with a value") }
                let lbl = self.loop_label(&dest)?;
                Ok(Tr::atom(match lbl { Some(l) => format!("break {};", l), None => "break;".into() }))
            }
            ExprKind::Continue(dest) => {
                let lbl = self.loop_label(&dest)?;
                Ok(Tr::atom(match lbl { Some(l) => format!("continue {};", l), None => "continue;".into() }))
            }
            ExprKind::Ret(v) => match v {
                Some(v) => {
                    let t = self.val(v)?;
                    Ok(Tr::atom(format!("return {};", t.s)))
                }
                None => Ok(Tr::atom("return;")),
            },
            ExprKind::Struct(qp, fields, tail) => self.struct_expr(e, qp, fields, tail),
            ExprKind::Array(es) => {
                if es.is_empty() { return Ok(Tr::atom("[]")) }
                let v: R<Vec<String>> = es.iter().map(|x| self.val(x).map(|t| t.s)).collect();
                Ok(Tr::atom(format!("[{}]", v?.join(", "))))
            }
            ExprKind::Repeat(..) => unsup("array repeat expression"),
            ExprKind::ConstBlock(..) => unsup("inline const block"),
            ExprKind::InlineAsm(..) => unsup("inline assembly"),
            ExprKind::OffsetOf(..) => unsup("offset_of"),
            ExprKind::Let(..) => unsup("`let` expression outside `if`"),
            ExprKind::Yield(..) => unsup("yield / await"),
            ExprKind::Become(..) => unsup("become"),
            ExprKind::Use(..) => unsup("ergonomic clone `use`"),
            ExprKind::UnsafeBinderCast(..) => unsup("unsafe binder cast"),
            ExprKind::Err(_) => unsup("error expression"),
            #[allow(unreachable_patterns)]
            _ => {
                let _ = tcx;
                unsup("expression kind")
            }
        }
    }

    fn loop_label(&mut self, dest: &hir::Destination) -> R<Option<String>> {
        let Ok(target) = dest.target_id else { return unsup("invalid loop target") };
        // the target must be a loop, not a labeled block
        match self.tcx.hir_node(target) {
            hir::Node::Expr(hir::Expr { kind: ExprKind::Loop(..), .. }) => {}
            _ => return unsup("`break`/`continue` targeting a labeled block"),
        }
        Ok(dest.label.map(|l| label_name(l.ident.as_str())))
    }

    // ------------------------------------------------------------------
    // Literals, paths, casts, operators
    // ------------------------------------------------------------------

    fn int_suffix(t: Ty<'tcx>) -> Option<&'static str> {
        Some(match t.kind() {
            ty::Uint(ty::UintTy::U8) => "u8",
            ty::Uint(ty::UintTy::U16) => "u16",
            ty::Uint(ty::UintTy::U32) => "u32",
            ty::Uint(ty::UintTy::U64) => "u64",
            ty::Uint(ty::UintTy::Usize) => "usize",
            ty::Int(ty::IntTy::I8) => "i8",
            ty::Int(ty::IntTy::I16) => "i16",
            ty::Int(ty::IntTy::I32) => "i32",
            ty::Int(ty::IntTy::I64) => "i64",
            ty::Int(ty::IntTy::Isize) => "isize",
            _ => return None,
        })
    }

    fn is_u64(t: Ty<'tcx>) -> bool {
        matches!(t.kind(), ty::Uint(ty::UintTy::U64) | ty::Uint(ty::UintTy::Usize))
    }

    fn int_lit(v: u128, t: Ty<'tcx>, neg: bool) -> R<Tr> {
        let Some(sfx) = Self::int_suffix(t) else { return unsup(format!("integer literal of type `{}`", t)) };
        if neg {
            Ok(Tr::new(format!("-{}_{}", v, sfx), 300))
        } else {
            Ok(Tr::atom(format!("{}_{}", v, sfx)))
        }
    }

    fn lit(&mut self, l: &LitKind, t: Ty<'tcx>, neg: bool) -> R<Tr> {
        match l {
            LitKind::Int(v, _) => {
                let _ = LitIntType::Unsuffixed;
                Self::int_lit(v.get(), t, neg)
            }
            LitKind::Bool(b) => Ok(Tr::atom(if *b { "true" } else { "false" })),
            LitKind::Byte(b) => Ok(Tr::atom(format!("{}_u8", b))),
            LitKind::Char(c) => Ok(Tr::atom(format!("\\<llangle>{}\\<rrangle>", hol_char(*c)?))),
            LitKind::Str(s, _) => {
                let s = s.as_str();
                if !names::hol_string_ok(s) { return unsup("string literal with non-ASCII or special characters") }
                Ok(Tr::atom(format!("\\<llangle>STR ''{}''\\<rrangle>", s)))
            }
            LitKind::Float(..) => unsup("floating-point literal"),
            LitKind::ByteStr(..) => unsup("byte string literal"),
            LitKind::CStr(..) => unsup("C string literal"),
            _ => unsup("literal"),
        }
    }

    fn path_value(&mut self, qp: &'tcx hir::QPath<'tcx>, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let res = self.typeck.qpath_res(qp, e.hir_id);
        match res {
            Res::Def(DefKind::Ctor(CtorOf::Struct, CtorKind::Const), ctor) => {
                let adt = self.tcx.parent(ctor);
                self.unit_ctor(adt, 0)
            }
            Res::Def(DefKind::Ctor(CtorOf::Variant, CtorKind::Const), ctor) => {
                let var = self.tcx.parent(ctor);
                let adt = self.tcx.parent(var);
                let vidx = self.tcx.adt_def(adt).variant_index_with_id(var).as_usize();
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
            Res::Def(DefKind::Fn | DefKind::AssocFn, _) => unsup("function item used as a value"),
            Res::Def(DefKind::Ctor(_, CtorKind::Fn), _) => unsup("constructor used as a function value"),
            _ => unsup(format!("path `{}`", self.fe.snippet(e.span))),
        }
    }

    fn unit_ctor(&mut self, adt: DefId, vidx: usize) -> R<Tr> {
        match self.fe.std_adt(adt) {
            Some("Option") => return Ok(Tr::atom("None")),
            Some("Ordering") => {
                let v = self.tcx.adt_def(adt).variant(vidx.into()).name.to_string();
                return Ok(Tr::atom(v));
            }
            _ => {}
        }
        if !adt.is_local() {
            // `core::panicking::AssertKind` only feeds the message of `assert_eq!`/`assert_ne!` failures
            if self.fe.is_std(adt) && self.tcx.def_path_str(adt).contains("panicking") {
                return Ok(Tr::atom("()"));
            }
            return unsup("constructor of an external type");
        }
        Ok(Tr::atom(self.fe.variant_ctor_name(adt, vidx)))
    }

    fn const_use(&mut self, did: DefId, e: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let t = self.ty_of(e);
        if let DefKind::Static { mutability, .. } = self.tcx.def_kind(did) {
            if mutability.is_mut() { return unsup("`static mut`") }
        }
        if did.is_local() {
            if self.tcx.hir_maybe_body_owned_by(did.expect_local()).is_some()
                && !self.tcx.generics_of(did).requires_monomorphization(self.tcx)
            {
                self.calls.insert(did);
                let m = self.fe.marker(did);
                return Ok(Tr::new(format!("\u{1}Z{}\u{2}", m), 999));
            }
        }
        // try to evaluate (e.g. `u32::MAX`)
        if t.is_integral() || t.is_bool() {
            if let Ok(v) = self.tcx.const_eval_poly(did) {
                if let Some(s) = v.try_to_scalar_int() {
                    if t.is_bool() {
                        return Ok(Tr::atom(if s.to_bits(s.size()) != 0 { "true" } else { "false" }));
                    }
                    let bits = s.to_bits(s.size());
                    if t.is_signed() {
                        let size = s.size().bits();
                        let sv = (bits as i128) << (128 - size) >> (128 - size);
                        if sv < 0 {
                            return Self::int_lit(sv.unsigned_abs(), t, true);
                        }
                        return Self::int_lit(sv as u128, t, false);
                    }
                    return Self::int_lit(bits, t, false);
                }
            }
        }
        unsup(format!("use of constant `{}`", self.tcx.def_path_str(did)))
    }

    fn cast(&mut self, x: &'tcx hir::Expr<'tcx>, target: Ty<'tcx>) -> R<Tr> {
        let src = self.ty_adj(x);
        let Some(tsfx) = Self::int_suffix(target) else { return unsup(format!("`as` cast to `{}`", target)) };
        if Self::int_suffix(src).is_none() { return unsup(format!("`as` cast from `{}`", src)) }
        let v = self.val(x)?;
        Ok(Tr::atom(format!("({}) as {}", v.s, tsfx)))
    }

    fn binop_info(op: BinOpKind) -> (&'static str, u32, bool) {
        // (token, precedence, left-assoc)
        match op {
            BinOpKind::Mul => ("*", 50, true),
            BinOpKind::Div => ("/", 50, true),
            BinOpKind::Rem => ("%", 50, true),
            BinOpKind::Add => ("+", 49, true),
            BinOpKind::Sub => ("-", 49, true),
            BinOpKind::Shl => ("<<", 48, true),
            BinOpKind::Shr => (">>", 48, true),
            BinOpKind::BitAnd => ("&", 47, true),
            BinOpKind::BitXor => ("^", 46, true),
            BinOpKind::BitOr => ("|", 45, true),
            BinOpKind::Eq => ("==", 44, false),
            BinOpKind::Ne => ("!=", 44, false),
            BinOpKind::Lt => ("<", 44, false),
            BinOpKind::Le => ("<=", 44, false),
            BinOpKind::Gt => (">", 44, false),
            BinOpKind::Ge => (">=", 44, false),
            BinOpKind::And => ("&&", 43, true),
            BinOpKind::Or => ("||", 42, true),
        }
    }

    fn mk_bin(op: &str, prec: u32, left_assoc: bool, l: &Tr, r: &Tr) -> Tr {
        let (lp, rp) = if left_assoc { (prec, prec + 1) } else { (prec + 1, prec + 1) };
        Tr::new(format!("{} {} {}", l.at(lp), op, r.at(rp)), prec)
    }

    fn binary(&mut self, e: &'tcx hir::Expr<'tcx>, op: BinOpKind, l: &'tcx hir::Expr<'tcx>, r: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        let lt = Self::peel_refs(self.ty_adj(l));
        let rt = Self::peel_refs(self.ty_adj(r));
        let prim = |t: Ty<'tcx>| t.is_integral() || t.is_bool() || t.is_char();
        let builtin = self.typeck.type_dependent_def_id(e.hir_id).is_none();
        if !(prim(lt) && prim(rt)) {
            // structural equality on types whose PartialEq is derived (or std)
            if matches!(op, BinOpKind::Eq | BinOpKind::Ne) && self.structural_eq(e) {
                let lv = self.val(l)?;
                let rv = self.val(r)?;
                let (tok, p, la) = Self::binop_info(op);
                return Ok(Self::mk_bin(tok, p, la, &lv, &rv));
            }
            if !builtin { return self.overloaded_op(e, &[l, r]) }
            return unsup(format!("binary operator on `{}`", lt));
        }
        let lv = self.val(l)?;
        let rv = self.val(r)?;
        if lt.is_bool() {
            let tok = match op {
                BinOpKind::BitAnd => "&&",
                BinOpKind::BitOr => "||",
                BinOpKind::BitXor => "!=",
                _ => Self::binop_info(op).0,
            };
            let (p, la) = match tok { "&&" => (43, true), "||" => (42, true), _ => (Self::binop_info(op).1, Self::binop_info(op).2) };
            if matches!(op, BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt | BinOpKind::Ge) {
                return unsup("ordering comparison on `bool`");
            }
            return Ok(Self::mk_bin(tok, p, la, &lv, &rv));
        }
        if lt.is_char() && !matches!(op, BinOpKind::Eq | BinOpKind::Ne) {
            return unsup("ordering comparison on `char`");
        }
        let rv = if matches!(op, BinOpKind::Shl | BinOpKind::Shr) && !Self::is_u64(rt) {
            // uRust shifts take a `64 word` shift amount
            match r.kind {
                ExprKind::Lit(hir::Lit { node: LitKind::Int(v, _), .. }) => Tr::atom(format!("{}_u64", v.get())),
                _ => Tr::atom(format!("({}) as u64", rv.s)),
            }
        } else {
            rv
        };
        let (tok, p, la) = Self::binop_info(op);
        Ok(Self::mk_bin(tok, p, la, &lv, &rv))
    }

    /// Is `==` on this expression structural (derived PartialEq or std impl on structural types)?
    fn structural_eq(&mut self, e: &'tcx hir::Expr<'tcx>) -> bool {
        let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else { return true };
        let args = self.typeck.node_args(e.hir_id);
        let env = ty::TypingEnv::post_analysis(self.tcx, self.owner.to_def_id());
        match ty::Instance::try_resolve(self.tcx, env, did, args) {
            Ok(Some(inst)) => {
                let rd = inst.def_id();
                if let Some(imp) = self.tcx.impl_of_assoc(rd) {
                    if self.tcx.is_automatically_derived(imp) { return true }
                    if !rd.is_local() {
                        // std impls (Option, tuples, references, str, slices) are structural
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Operator resolved to a trait method (e.g. `impl Add for Point`).
    fn overloaded_op(&mut self, e: &'tcx hir::Expr<'tcx>, operands: &[&'tcx hir::Expr<'tcx>]) -> R<Tr> {
        let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else {
            return unsup("operator on a non-primitive type");
        };
        let args = self.typeck.node_args(e.hir_id);
        let mut argv = vec![];
        for o in operands { argv.push(self.val(o)?); }
        self.call_def(did, args, argv, operands, e)
    }

    fn assign_op(&mut self, e: &'tcx hir::Expr<'tcx>, op: hir::AssignOpKind, lhs: &'tcx hir::Expr<'tcx>, rhs: &'tcx hir::Expr<'tcx>) -> R<Tr> {
        use hir::AssignOpKind as A;
        let lt = Self::peel_refs(self.ty_adj(lhs));
        if !(lt.is_integral() || lt.is_bool()) || self.typeck.type_dependent_def_id(e.hir_id).is_some() && !lt.is_integral() {
            // overloaded compound assignment: call `T::add_assign(&mut lhs, rhs)`
            let Some(did) = self.typeck.type_dependent_def_id(e.hir_id) else { return unsup("compound assignment") };
            let args = self.typeck.node_args(e.hir_id);
            let p = self.place(lhs)?;
            let v = self.val(rhs)?;
            return self.call_def(did, args, vec![p, v], &[lhs, rhs], e);
        }
        let p = self.place(lhs)?;
        let mut v = self.val(rhs)?;
        let tok = match op {
            A::AddAssign => "+=",
            A::SubAssign => "-=",
            A::MulAssign => "*=",
            A::RemAssign => "%=",
            A::BitAndAssign => "&=",
            A::BitOrAssign => "|=",
            A::BitXorAssign => "^=",
            A::ShlAssign | A::ShrAssign => {
                let rt = Self::peel_refs(self.ty_adj(rhs));
                if !Self::is_u64(rt) {
                    v = match rhs.kind {
                        ExprKind::Lit(hir::Lit { node: LitKind::Int(n, _), .. }) => Tr::atom(format!("{}_u64", n.get())),
                        _ => Tr::atom(format!("({}) as u64", v.s)),
                    };
                }
                if matches!(op, A::ShlAssign) { "<<=" } else { ">>=" }
            }
            A::DivAssign => {
                // `x /= e` is not in uRust; desugar to `x = *x / e` (the place is evaluated twice,
                // which is only done for places without side effects).
                if p.s.contains('(') && p.s.contains("\u{1}") { return unsup("`/=` on a place with calls") }
                return Ok(Tr::new(format!("*{} = *{} / {}", p.at(200), p.at(200), v.at(51)), 40));
            }
        };
        if lt.is_bool() {
            let t2 = match op { A::BitAndAssign => "&&", A::BitOrAssign => "||", A::BitXorAssign => "!=", _ => return unsup("compound assignment on bool") };
            return Ok(Tr::new(format!("*{} = *{} {} {}", p.at(200), p.at(200), t2, v.at(45)), 40));
        }
        Ok(Tr::new(format!("*{} {} {}", p.at(200), tok, v.at(40)), 40))
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
                if let Some(t) = self.panic_or_print(did, args)? {
                    return Ok(t);
                }
                let gargs = self.typeck.node_args(callee.hir_id);
                let mut argv = vec![];
                for a in args { argv.push(self.val(a)?); }
                let arg_exprs: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
                self.call_def(did, gargs, argv, &arg_exprs, e)
            }
            Res::Def(DefKind::Ctor(of, CtorKind::Fn), ctor) => {
                let (adt, vidx) = match of {
                    CtorOf::Struct => (self.tcx.parent(ctor), 0),
                    CtorOf::Variant => {
                        let var = self.tcx.parent(ctor);
                        let adt = self.tcx.parent(var);
                        (adt, self.tcx.adt_def(adt).variant_index_with_id(var).as_usize())
                    }
                };
                let mut argv = vec![];
                for a in args { argv.push(self.val(a)?); }
                self.ctor_call(adt, vidx, argv)
            }
            Res::SelfCtor(_) => {
                let t = self.ty_of(e);
                let ty::Adt(def, _) = t.kind() else { return unsup("Self constructor") };
                let mut argv = vec![];
                for a in args { argv.push(self.val(a)?); }
                self.ctor_call(def.did(), 0, argv)
            }
            Res::Local(hid) => {
                let Some(l) = self.locals.get(&hid).cloned() else { return unsup("call of unknown local") };
                if l.cell { return unsup("call of a closure stored in a mutable local") }
                let mut argv = vec![];
                for a in args { argv.push(self.val(a)?.s); }
                if argv.is_empty() { Ok(Tr::new(format!("{}()", l.name), 999)) } else {
                    if argv.len() > 8 { return unsup("call with more than 8 arguments") }
                    Ok(Tr::new(format!("{}({})", l.name, argv.join(", ")), 999))
                }
            }
            _ => unsup("call target"),
        }
    }

    /// Panics and printing from the standard library (recognised before their
    /// `format_args!` arguments are translated).
    fn panic_or_print(&mut self, did: DefId, args: &'tcx [hir::Expr<'tcx>]) -> R<Option<Tr>> {
        if !self.fe.is_std(did) {
            return Ok(None);
        }
        let path = self.tcx.def_path_str(did);
        if path.contains("fmt::format") || path.contains("fmt::Arguments") {
            return unsup("string formatting (format!)");
        }
        if path.contains("panicking") || path.contains("begin_panic") {
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
            let lit = args.iter().find_map(|x| find_str(x));
            let msg = lit.unwrap_or_else(|| {
                if path.contains("assert_failed") { "assertion failed".into() } else { "panic".into() }
            });
            return Ok(Some(Tr::new(format!("panic!(\"{}\")", names::string_token(&msg)), 999)));
        }
        if path.ends_with("io::_print") || path.ends_with("io::_eprint") {
            self.comments.push("output (print!/println!) is not modelled and was dropped".into());
            return Ok(Some(Tr::atom("()")));
        }
        Ok(None)
    }

    fn ctor_call(&mut self, adt: DefId, vidx: usize, argv: Vec<Tr>) -> R<Tr> {
        if let Some(k) = self.fe.std_adt(adt) {
            let vname = self.tcx.adt_def(adt).variant(vidx.into()).name.to_string();
            return match (k, vname.as_str()) {
                ("Option", "Some") | ("Result", "Ok") | ("Result", "Err") => {
                    Ok(Tr::new(format!("{}({})", vname, argv[0].s), 999))
                }
                _ => unsup("constructor of a standard library type"),
            };
        }
        if !adt.is_local() { return unsup("constructor of an external type") }
        if argv.len() > 8 { return unsup("constructor with more than 8 fields") }
        let n = self.fe.variant_call_name(adt, vidx);
        let a: Vec<String> = argv.into_iter().map(|t| t.s).collect();
        Ok(Tr::new(format!("{}({})", n, a.join(", ")), 999))
    }

    fn local_call(&mut self, did: DefId, argv: Vec<Tr>) -> R<Tr> {
        if self.fe.is_trait_item(did) { return unsup("call of a trait default method") }
        self.calls.insert(did);
        let m = self.fe.marker(did);
        let a: Vec<String> = argv.iter().map(|t| t.s.clone()).collect();
        Ok(self.callee_app(&format!("\u{1}C{}\u{2}", m), &format!("\u{1}H{}\u{2}", m), &format!("\u{1}Z{}\u{2}", m), a))
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
        let a: Vec<String> = argv.into_iter().map(|t| t.s).collect();
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
        if self.fe.local_fn_with_body(did) && !self.fe.is_trait_item(did) {
            return self.local_call(did, argv);
        }
        // trait methods: resolve to the implementation
        let mut target = did;
        if self.tcx.trait_of_assoc(did).is_some() {
            let env = ty::TypingEnv::post_analysis(self.tcx, self.owner.to_def_id());
            match ty::Instance::try_resolve(self.tcx, env, did, gargs) {
                Ok(Some(inst)) => {
                    match inst.def {
                        ty::InstanceKind::Item(rd) => target = rd,
                        ty::InstanceKind::Virtual(..) => return unsup("dynamic dispatch (trait object)"),
                        _ => {
                            // compiler-generated shims, e.g. `Clone` for primitive/tuple types
                            if let Some(t) = self.std_call(did, did, argv.clone(), arg_exprs, e)? { return Ok(t) }
                            return unsup(format!("call of `{}`", self.tcx.def_path_str(did)));
                        }
                    }
                }
                _ => return unsup("trait method call in generic code (needs monomorphisation)"),
            }
            if target.is_local() {
                let derived = self.tcx.impl_of_assoc(target).map(|i| self.tcx.is_automatically_derived(i)).unwrap_or(false);
                if !derived {
                    if self.fe.is_trait_item(target) { return unsup("call of a trait default method") }
                    return self.local_call(target, argv);
                }
            }
        }
        // functions declared in `extern` blocks: emit a foreign template definition
        if self.tcx.is_foreign_item(target) {
            let n = self.fe.ext_fun(target, true);
            return Ok(self.named_call(&n, argv));
        }
        // methods of types with interior mutability cannot be modelled by values
        let mut tys: Vec<Ty<'tcx>> = arg_exprs.iter().take(1).map(|a| self.ty_adj(a)).collect();
        tys.push(self.ty_of(e));
        for t in tys {
            if let ty::Adt(d, _) = Self::peel_refs(t).kind() {
                let n = self.tcx.item_name(d.did()).to_string();
                if self.fe.is_std(d.did())
                    && (matches!(n.as_str(), "Cell" | "RefCell" | "UnsafeCell" | "OnceCell" | "Mutex" | "RwLock")
                        || n.starts_with("Atomic"))
                {
                    return unsup(format!("interior mutability (`{}`)", n));
                }
            }
        }
        if let Some(t) = self.std_call(did, target, argv.clone(), arg_exprs, e)? {
            return Ok(t);
        }
        if target.is_local() {
            return unsup(format!("call of `{}`", self.tcx.def_path_str(target)));
        }
        if self.tcx.generics_of(target).has_self && self.tcx.trait_of_assoc(target).is_some() {
            return unsup(format!("call of trait method `{}`", self.tcx.def_path_str(target)));
        }
        let n = self.fe.ext_fun(target, false);
        Ok(self.named_call(&n, argv))
    }

    /// Key used for the standard library table: (type or trait name, item name).
    fn std_key(&self, did: DefId) -> (String, String) {
        let name = self.tcx.item_name(did).to_string();
        let parent = self.tcx.parent(did);
        let owner = match self.tcx.def_kind(parent) {
            DefKind::Impl { .. } => {
                if let Some(tr) = self.tcx.impl_opt_trait_ref(parent) {
                    self.tcx.item_name(tr.skip_binder().def_id).to_string()
                } else {
                    self.fe.short_ty_name(self.tcx.type_of(parent).instantiate_identity().skip_normalization())
                }
            }
            DefKind::Trait => self.tcx.item_name(parent).to_string(),
            _ => self.tcx.opt_item_name(parent).map(|s| s.to_string()).unwrap_or_default(),
        };
        (owner, name)
    }

    fn std_call(
        &mut self,
        orig: DefId,
        target: DefId,
        argv: Vec<Tr>,
        arg_exprs: &[&'tcx hir::Expr<'tcx>],
        e: &'tcx hir::Expr<'tcx>,
    ) -> R<Option<Tr>> {
        let (tk, tn) = self.std_key(orig);
        let (ik, iname) = self.std_key(target);
        let a = |i: usize| -> Tr { argv[i].clone() };
        let same_hol = |this: &mut Self| -> bool {
            if arg_exprs.is_empty() { return false }
            let src = Self::peel_refs(this.ty_adj(arg_exprs[0]));
            let dst = Self::peel_refs(this.ty_of(e));
            this.fe.ty(src) == this.fe.ty(dst)
        };
        let crate_ = self.fe.crate_of(target);
        let path = self.tcx.def_path_str(target);
        let is_std = matches!(crate_.as_str(), "core" | "alloc" | "std");
        // panics
        if is_std && (path.contains("panicking") || path.contains("begin_panic")) {
            let msg = arg_exprs.first().and_then(|x| match x.kind {
                ExprKind::Lit(l) => match l.node { LitKind::Str(s, _) => Some(s.to_string()), _ => None },
                _ => None,
            });
            let msg = msg.unwrap_or_else(|| if path.contains("assert_failed") { "assertion failed".into() } else { "panic".into() });
            return Ok(Some(Tr::new(format!("panic!(\"{}\")", names::string_token(&msg)), 999)));
        }
        if is_std && (path.ends_with("io::_print") || path.ends_with("io::_eprint")) {
            self.comments.push("output (print!/println!) is not modelled and was dropped".into());
            return Ok(Some(Tr::atom("()")));
        }
        let r = match (tk.as_str(), tn.as_str()) {
            ("Clone", "clone") if !target.is_local() || self.derived(target) => Some(self.deref_arg(a(0), arg_exprs, 0)),
            ("PartialEq", "eq") if !target.is_local() || self.derived(target) => {
                Some(Self::mk_bin("==", 44, false, &self.deref_arg(a(0), arg_exprs, 0), &self.deref_arg(a(1), arg_exprs, 1)))
            }
            ("PartialEq", "ne") if !target.is_local() || self.derived(target) => {
                Some(Self::mk_bin("!=", 44, false, &self.deref_arg(a(0), arg_exprs, 0), &self.deref_arg(a(1), arg_exprs, 1)))
            }
            ("Ord", "cmp") if !target.is_local() => Some(self.named_call("cmp", vec![a(0), a(1)])),
            ("Option", "unwrap") => Some(self.named_call("option_unwrap", vec![a(0)])),
            ("Option", "expect") => Some(self.named_call("option_expect", vec![a(0), a(1)])),
            ("Option", "is_some") => Some(self.named_call("urust_func_option_is_some", vec![a(0)])),
            ("Option", "is_none") => Some(self.named_call("urust_func_option_is_none", vec![a(0)])),
            ("Option", "ok_or") => Some(self.named_call("ok_or", vec![a(0), a(1)])),
            ("Option", "take") => Some(self.named_call("take_mut_ref_option", vec![a(0)])),
            ("Result", "unwrap") => Some(self.named_call("result_unwrap", vec![a(0)])),
            ("Result", "expect") => Some(self.named_call("result_expect", vec![a(0), a(1)])),
            ("Result", "is_ok") => Some(self.named_call("urust_func_result_is_ok", vec![a(0)])),
            ("Result", "is_err") => Some(self.named_call("urust_func_result_is_err", vec![a(0)])),
            ("Result", "ok") => Some(self.named_call("ok", vec![a(0)])),
            ("Result", "unwrap_or") => Some(self.named_call("result_unwrap_or", vec![a(0), a(1)])),
            ("Vec", "len") | ("slice", "len") | ("array", "len") => Some(self.named_call("len", vec![a(0)])),
            ("Vec", "new") | ("Vec", "with_capacity") if argv.len() <= 1 => Some(Tr::atom("[]")),
            ("slice", "into_vec") | ("slice", "to_vec") => Some(a(0)),
            ("Box", "new") => Some(a(0)),
            ("mem", "drop") => Some(Tr::atom(format!("{{ let _ = {}; () }}", a(0).s))),
            ("RangeInclusive", "new") => Some(Tr::new(format!("{} ..= {}", a(0).at(42), a(1).at(42)), 41)),
            ("ToString", "to_string") | ("ToOwned", "to_owned") | ("From", "from") | ("Into", "into")
            | ("String", "from") | ("AsRef", "as_ref") | ("Borrow", "borrow") | ("Vec", "as_slice")
            | ("String", "as_str") | ("slice", "iter") | ("Vec", "iter")
                if same_hol(self) =>
            {
                Some(a(0))
            }
            (k, "checked_add") | (k, "checked_mul") | (k, "saturating_sub") | (k, "wrapping_add") | (k, "div_ceil")
                if k.starts_with('u') =>
            {
                let f = match tn.as_str() {
                    "wrapping_add" => "wrapping_add_unsigned",
                    x => x,
                };
                Some(self.named_call(f, vec![a(0), a(1)]))
            }
            _ => None,
        };
        let _ = (ik, iname);
        Ok(r)
    }

    fn derived(&self, did: DefId) -> bool {
        self.tcx.impl_of_assoc(did).map(|i| self.tcx.is_automatically_derived(i)).unwrap_or(false)
    }

    /// Arguments of `Clone::clone(&x)` / `PartialEq::eq(&a, &b)` are shared references,
    /// which are already values in our representation.
    fn deref_arg(&self, t: Tr, _exprs: &[&'tcx hir::Expr<'tcx>], _i: usize) -> Tr { t }

    // ------------------------------------------------------------------
    // Structs
    // ------------------------------------------------------------------

    fn struct_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        _qp: &'tcx hir::QPath<'tcx>,
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
                    if f.ident.as_str() == "start" { st = Some(v) } else { en = Some(v) }
                }
                let (Some(a), Some(b)) = (st, en) else { return unsup("range") };
                return Ok(Tr::new(format!("{} .. {}", a.at(42), b.at(42)), 41));
            }
            return unsup(format!("struct expression of `{}`", t));
        }
        if !adt.is_local() || def.is_union() { return unsup(format!("struct expression of `{}`", t)) }
        let res = self.typeck.qpath_res(_qp, e.hir_id);
        let variant = def.variant_of_res(res);
        let vidx = def.variants().iter().position(|v| v.def_id == variant.def_id).unwrap_or(0);
        let nf = variant.fields.len();
        let mut vals: Vec<Option<Tr>> = vec![None; nf];
        let mut pre = vec![];
        // evaluate the written fields in source order (bound to temporaries when there are calls)
        let need_tmp = fields.len() > 1 && fields.iter().any(|f| matches!(f.expr.kind, ExprKind::Call(..) | ExprKind::MethodCall(..)));
        for f in fields {
            let idx = self.typeck.field_index(f.hir_id).as_usize();
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
        let vals: Vec<Tr> = vals.into_iter().map(|v| v.unwrap_or(Tr::atom("\\<llangle>undefined\\<rrangle>"))).collect();
        let core = if nf == 0 {
            Tr::atom(self.fe.variant_ctor_name(adt, vidx))
        } else if def.is_enum() {
            self.ctor_call(adt, vidx, vals)?
        } else {
            if nf > 8 { return unsup("struct with more than 8 fields") }
            let n = self.fe.variant_call_name(adt, vidx);
            let fs: Vec<String> = (0..nf).map(|k| {
                let fname = self.fe.field_name(adt, vidx, k);
                format!("{}: {}", fname, vals[k].s)
            }).collect();
            Tr::atom(format!("{} {{ {} }}", n, fs.join(", ")))
        };
        if pre.is_empty() { Ok(core) } else { Ok(Tr::atom(format!("{{\n{}\n{}\n}}", pre.join("\n"), core.s))) }
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
            let iv = self.val(le.init)?;
            let p = self.pat(le.pat)?;
            let mut tb = p.prologue.join("\n");
            if !tb.is_empty() { tb.push('\n'); }
            tb.push_str(&self.branch(t)?);
            let eb = match el { Some(x) => self.branch(x)?, None => "()".into() };
            if p.conds.is_empty() {
                return Ok(Tr::new(format!("if let {} = {} {{\n{}\n}} else {{\n{}\n}}", p.pat, iv.at(20), tb, eb), 11));
            }
            return Ok(Tr::new(format!(
                "match {} {{\n  {} if {} \\<Rightarrow> {{\n{}\n}},\n  _ \\<Rightarrow> {{\n{}\n}}\n}}",
                iv.at(20), p.pat, p.conds.join(" && "), tb, eb
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

    fn label_prefix(label: Option<rustc_ast::Label>) -> String {
        match label { Some(l) => format!("{}: ", label_name(l.ident.as_str())), None => String::new() }
    }

    fn loop_expr(&mut self, e: &'tcx hir::Expr<'tcx>, b: &'tcx hir::Block<'tcx>, label: Option<rustc_ast::Label>, src: LoopSource) -> R<Tr> {
        let lp = Self::label_prefix(label);
        let _ = e;
        match src {
            LoopSource::While => {
                // loop { if cond { body } else { break } }
                let Some(ife) = b.expr else { return unsup("while desugaring") };
                let ExprKind::If(cond, then, _) = ife.kind else { return unsup("while desugaring") };
                let cond = Self::strip_drop_temps(cond);
                if let ExprKind::Let(le) = cond.kind {
                    let iv = self.val(le.init)?;
                    let p = self.pat(le.pat)?;
                    let mut body = p.prologue.join("\n");
                    if !body.is_empty() { body.push('\n'); }
                    body.push_str(&self.branch(then)?);
                    if p.conds.is_empty() {
                        return Ok(Tr::new(format!("{} {}while let {} = {} {{\n{}\n}}", FUEL, lp, p.pat, iv.at(20), body), 11));
                    }
                    return Ok(Tr::new(format!(
                        "{} {}loop {{\nmatch {} {{\n  {} if {} \\<Rightarrow> {{\n{}\n}},\n  _ \\<Rightarrow> {{ break; }}\n}};\n}}",
                        FUEL, lp, iv.at(20), p.pat, p.conds.join(" && "), body
                    ), 11));
                }
                if contains_let(cond) { return unsup("`let` chain in `while` condition") }
                let cv = self.val(cond)?;
                let body = self.branch(then)?;
                Ok(Tr::new(format!("{} {}while {} {{\n{}\n}}", FUEL, lp, cv.at(20), body), 11))
            }
            LoopSource::Loop => {
                let body = self.block_seq(b.stmts, b.expr)?;
                Ok(Tr::new(format!("{} {}loop {{\n{}\n}}", FUEL, lp, body), 11))
            }
            LoopSource::ForLoop => unsup("for-loop desugaring"),
        }
    }

    fn for_loop(&mut self, _e: &'tcx hir::Expr<'tcx>, head_call: &'tcx hir::Expr<'tcx>, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        // match IntoIterator::into_iter(<head>) { mut iter => loop { match next(&mut iter) { None => break, Some(<pat>) => <body> } } }
        let ExprKind::Call(_, [head]) = head_call.kind else { return unsup("for-loop head") };
        let [arm] = arms else { return unsup("for-loop desugaring") };
        let ExprKind::Loop(lb, label, LoopSource::ForLoop, _) = arm.body.kind else { return unsup("for-loop desugaring") };
        let inner_match = lb.stmts.iter().find_map(|s| match s.kind {
            StmtKind::Expr(x) | StmtKind::Semi(x) => match x.kind {
                ExprKind::Match(_, arms2, MatchSource::ForLoopDesugar) => Some(arms2),
                _ => None,
            },
            _ => None,
        }).or_else(|| lb.expr.and_then(|x| match x.kind {
            ExprKind::Match(_, arms2, MatchSource::ForLoopDesugar) => Some(arms2),
            _ => None,
        }));
        let Some(arms2) = inner_match else { return unsup("for-loop desugaring") };
        // `Some { 0: pat } => body` (a struct pattern in current HIR; a tuple-struct pattern in older ones)
        let some = arms2.iter().find_map(|a| match a.pat.kind {
            PatKind::TupleStruct(_, [p], _) => Some((a, p)),
            PatKind::Struct(_, [f], _) => Some((a, f.pat)),
            _ => None,
        });
        let Some((some_arm, pat)) = some else { return unsup("for-loop desugaring") };
        // the iterable
        let ht = self.ty_of(head);
        let iter_s = match Self::peel_refs(ht).kind() {
            ty::Adt(def, _) if matches!(self.fe.std_adt(def.did()), Some("Range") | Some("RangeInclusive")) => self.val(head)?,
            ty::Adt(def, _) if self.fe.std_adt(def.did()) == Some("Vec") => self.val(head)?,
            ty::Slice(_) | ty::Array(..) => self.val(head)?,
            ty::Adt(def, _) if self.tcx.item_name(def.did()).as_str() == "Iter" && self.fe.is_std(def.did()) => {
                // `xs.iter()` over a slice / Vec
                match head.kind {
                    ExprKind::MethodCall(seg, recv, [], _) if seg.ident.as_str() == "iter" => self.val(recv)?,
                    _ => return unsup("for-loop over an iterator adaptor"),
                }
            }
            _ => return unsup(format!("for-loop over `{}`", ht)),
        };
        // the loop pattern
        let mut pro = vec![];
        let ps = match pat.kind {
            PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, None) => {
                let n = names::local_name(ident.as_str());
                if m.is_mut() {
                    let t = self.typeck.node_type(hid);
                    self.alloc(t, pat.span)?;
                    pro.push(format!("let mut {} = {};", n, n));
                    self.locals.insert(hid, Local { name: n.clone(), cell: true });
                } else {
                    self.locals.insert(hid, Local { name: n.clone(), cell: false });
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
        let mut body = pro.join("\n");
        if !body.is_empty() { body.push('\n'); }
        body.push_str(&self.branch(some_arm.body)?);
        let lp = Self::label_prefix(label);
        Ok(Tr::new(format!("{}for {} in {} {{\n{}\n}}", lp, ps, iter_s.at(20), body), 11))
    }

    // ------------------------------------------------------------------
    // match
    // ------------------------------------------------------------------

    fn int_like(&self, t: Ty<'tcx>) -> bool {
        let t = Self::peel_refs(t);
        t.is_integral() || t.is_char() || t.is_str() || matches!(t.kind(), ty::Adt(d, _) if self.fe.std_adt(d.did()) == Some("String"))
    }

    fn match_expr(&mut self, scrut: &'tcx hir::Expr<'tcx>, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        let st = self.ty_adj(scrut);
        let sv = self.val(scrut)?;
        if self.int_like(st) {
            return self.match_chain(sv, arms);
        }
        let mut out = vec![];
        for arm in arms {
            let p = self.pat(arm.pat)?;
            let mut conds = p.conds.clone();
            if let Some(g) = arm.guard {
                if contains_let(g) { return unsup("`if let` guard") }
                let gv = self.val(g)?;
                conds.push(gv.at(44));
            }
            let mut body = p.prologue.join("\n");
            if !body.is_empty() { body.push('\n'); }
            body.push_str(&self.branch(arm.body)?);
            let guard = if conds.is_empty() { String::new() } else { format!(" if {}", conds.join(" && ")) };
            out.push(format!("  {}{} \\<Rightarrow> {{\n{}\n}}", p.pat, guard, body));
        }
        Ok(Tr::new(format!("match {} {{\n{}\n}}", sv.at(20), out.join(",\n")), 20))
    }

    /// `match` on integers / chars / strings as an `if` chain.
    fn match_chain(&mut self, sv: Tr, arms: &'tcx [hir::Arm<'tcx>]) -> R<Tr> {
        let tmp = self.fresh("scrut");
        let tv = Tr::atom(tmp.clone());
        let mut branches: Vec<(Option<String>, String)> = vec![];
        for arm in arms {
            let (cond, binds) = self.pat_cond(arm.pat, &tv)?;
            let mut body = binds.join("\n");
            if !body.is_empty() { body.push('\n'); }
            body.push_str(&self.branch(arm.body)?);
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
        let mut acc: Option<String> = None;
        for (cond, body) in branches.into_iter().rev() {
            acc = Some(match (cond, acc) {
                (None, _) => body,
                (Some(c), None) => format!("if {} {{\n{}\n}} else {{\n panic!(\"non-exhaustive match\")\n}}", c, body),
                (Some(c), Some(rest)) => format!("if {} {{\n{}\n}} else {{\n{}\n}}", c, body, rest),
            });
        }
        let acc = acc.unwrap_or_else(|| "panic!(\"empty match\")".into());
        Ok(Tr::atom(format!("{{\nlet {} = {};\n{}\n}}", tmp, sv.at(20), acc)))
    }

    /// Condition + bindings for a pattern matched against a value (used for scalar matches).
    fn pat_cond(&mut self, pat: &'tcx hir::Pat<'tcx>, v: &Tr) -> R<(Option<String>, Vec<String>)> {
        match pat.kind {
            PatKind::Wild => Ok((None, vec![])),
            PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, sub) => {
                let n = names::local_name(ident.as_str());
                let mut binds = vec![];
                if m.is_mut() {
                    let t = self.typeck.node_type(hid);
                    self.alloc(t, pat.span)?;
                    binds.push(format!("let mut {} = {};", n, v.at(20)));
                    self.locals.insert(hid, Local { name: n.clone(), cell: true });
                } else {
                    binds.push(format!("let {} = {};", n, v.at(20)));
                    self.locals.insert(hid, Local { name: n.clone(), cell: false });
                }
                match sub {
                    Some(s) => {
                        let (c, b2) = self.pat_cond(s, v)?;
                        binds.extend(b2);
                        Ok((c, binds))
                    }
                    None => Ok((None, binds)),
                }
            }
            PatKind::Binding(..) => unsup("`ref` binding"),
            PatKind::Expr(pe) => Ok((Some(format!("{} == {}", v.at(45), self.pat_expr(pe, pat)?.at(45))), vec![])),
            PatKind::Range(lo, hi, end) => {
                let mut cs = vec![];
                if let Some(lo) = lo { cs.push(format!("{} <= {}", self.pat_expr(lo, pat)?.at(45), v.at(45))); }
                if let Some(hi) = hi {
                    let op = if matches!(end, hir::RangeEnd::Included) { "<=" } else { "<" };
                    cs.push(format!("{} {} {}", v.at(45), op, self.pat_expr(hi, pat)?.at(45)));
                }
                if self.ty_is_char(pat) { return unsup("range pattern on `char`") }
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
            PatKind::Ref(p, _, _) | PatKind::Deref(p) => self.pat_cond(p, v),
            _ => unsup("pattern in a match on a scalar"),
        }
    }

    fn ty_is_char(&self, pat: &'tcx hir::Pat<'tcx>) -> bool {
        Self::peel_refs(self.typeck.pat_ty(pat)).is_char()
    }

    /// A literal / constant inside a pattern, as a uRust value.
    fn pat_expr(&mut self, pe: &'tcx hir::PatExpr<'tcx>, pat: &'tcx hir::Pat<'tcx>) -> R<Tr> {
        let t = Self::peel_refs(self.typeck.node_type(pe.hir_id));
        let t = if t.is_integral() || t.is_char() || t.is_bool() || t.is_str() { t } else { Self::peel_refs(self.typeck.pat_ty(pat)) };
        match pe.kind {
            hir::PatExprKind::Lit { lit, negated } => {
                if let LitKind::Str(..) = lit.node {
                    return self.lit(&lit.node, t, false);
                }
                self.lit(&lit.node, t, negated)
            }
            hir::PatExprKind::Path(ref qp) => {
                let res = self.typeck.qpath_res(qp, pe.hir_id);
                match res {
                    Res::Def(DefKind::Const | DefKind::AssocConst { .. }, did) => {
                        if t.is_integral() || t.is_bool() {
                            if let Ok(v) = self.tcx.const_eval_poly(did) {
                                if let Some(s) = v.try_to_scalar_int() {
                                    let bits = s.to_bits(s.size());
                                    if t.is_bool() { return Ok(Tr::atom(if bits != 0 { "true" } else { "false" })) }
                                    if t.is_signed() {
                                        let size = s.size().bits();
                                        let sv = (bits as i128) << (128 - size) >> (128 - size);
                                        return if sv < 0 { Self::int_lit(sv.unsigned_abs(), t, true) } else { Self::int_lit(sv as u128, t, false) };
                                    }
                                    return Self::int_lit(bits, t, false);
                                }
                            }
                        }
                        unsup("constant in pattern")
                    }
                    _ => unsup("path in pattern expression"),
                }
            }
        }
    }

    /// Translate a refutable pattern for a uRust `match` / `if let`.
    fn pat(&mut self, pat: &'tcx hir::Pat<'tcx>) -> R<PatTr> {
        let mut conds = vec![];
        let mut prologue = vec![];
        let s = self.pat_rec(pat, &mut conds, &mut prologue, true)?;
        Ok(PatTr { pat: s, conds, prologue })
    }

    fn pat_rec(&mut self, pat: &'tcx hir::Pat<'tcx>, conds: &mut Vec<String>, pro: &mut Vec<String>, top: bool) -> R<String> {
        let _ = top;
        match pat.kind {
            PatKind::Wild => Ok("_".into()),
            PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, sub) => {
                // binding mode after match ergonomics
                if let Some(bm) = self.typeck.pat_binding_modes().get(hid) {
                    if let hir::ByRef::Yes(_, mutbl) = bm.0 {
                        if mutbl.is_mut() { return unsup("binding by mutable reference (match ergonomics)") }
                    }
                }
                let n = names::local_name(ident.as_str());
                let n = format!("{}", n);
                if m.is_mut() {
                    let t = self.typeck.node_type(hid);
                    self.alloc(t, pat.span)?;
                    pro.push(format!("let mut {} = {};", n, n));
                    self.locals.insert(hid, Local { name: n.clone(), cell: true });
                } else {
                    self.locals.insert(hid, Local { name: n.clone(), cell: false });
                }
                match sub {
                    None => Ok(n),
                    Some(s) => {
                        let inner = self.pat_rec(s, conds, pro, false)?;
                        Ok(format!("{} @ {}", n, if inner.contains(' ') { format!("({})", inner) } else { inner }))
                    }
                }
            }
            PatKind::Binding(..) => unsup("`ref` binding"),
            PatKind::Tuple(ps, ddpos) => {
                let t = Self::peel_refs(self.typeck.pat_ty(pat));
                let n = match t.kind() { ty::Tuple(ts) => ts.len(), _ => ps.len() };
                if n < 2 { return unsup("tuple pattern with fewer than 2 components") }
                let mut parts = vec![];
                for p in expand_dotdot(ps, ddpos, n) {
                    parts.push(match p { Some(p) => self.pat_rec(p, conds, pro, false)?, None => "_".into() });
                }
                Ok(format!("({})", parts.join(", ")))
            }
            PatKind::TupleStruct(ref qp, ps, ddpos) => {
                let (adt, vidx) = self.pat_variant(qp, pat)?;
                let n = self.tcx.adt_def(adt).variant(vidx.into()).fields.len();
                let mut parts = vec![];
                for p in expand_dotdot(ps, ddpos, n) {
                    parts.push(match p { Some(p) => self.pat_rec(p, conds, pro, false)?, None => "_".into() });
                }
                self.ctor_pat(adt, vidx, parts)
            }
            PatKind::Struct(ref qp, fields, _) => {
                let (adt, vidx) = self.pat_variant(qp, pat)?;
                let n = self.tcx.adt_def(adt).variant(vidx.into()).fields.len();
                let mut parts = vec!["_".to_string(); n];
                for f in fields.iter() {
                    let idx = self.typeck.field_index(f.hir_id).as_usize();
                    parts[idx] = self.pat_rec(f.pat, conds, pro, false)?;
                }
                self.ctor_pat(adt, vidx, parts)
            }
            PatKind::Expr(pe) => {
                if let hir::PatExprKind::Path(ref qp) = pe.kind {
                    let res = self.typeck.qpath_res(qp, pe.hir_id);
                    match res {
                        Res::Def(DefKind::Ctor(CtorOf::Variant, CtorKind::Const), ctor) => {
                            let var = self.tcx.parent(ctor);
                            let adt = self.tcx.parent(var);
                            let vidx = self.tcx.adt_def(adt).variant_index_with_id(var).as_usize();
                            return self.ctor_pat(adt, vidx, vec![]);
                        }
                        Res::Def(DefKind::Ctor(CtorOf::Struct, CtorKind::Const), ctor) => {
                            let adt = self.tcx.parent(ctor);
                            return self.ctor_pat(adt, 0, vec![]);
                        }
                        _ => {}
                    }
                }
                let t = Self::peel_refs(self.typeck.pat_ty(pat));
                if t.is_bool() {
                    if let hir::PatExprKind::Lit { lit, .. } = pe.kind {
                        if let LitKind::Bool(b) = lit.node { return Ok(if b { "true".into() } else { "false".into() }) }
                    }
                }
                let v = self.pat_expr(pe, pat)?;
                let tmp = self.fresh("lit");
                conds.push(format!("{} == {}", tmp, v.at(45)));
                Ok(tmp)
            }
            PatKind::Range(lo, hi, end) => {
                if self.ty_is_char(pat) { return unsup("range pattern on `char`") }
                let tmp = self.fresh("rng");
                let tv = Tr::atom(tmp.clone());
                if let Some(lo) = lo { conds.push(format!("{} <= {}", self.pat_expr(lo, pat)?.at(45), tv.s)); }
                if let Some(hi) = hi {
                    let op = if matches!(end, hir::RangeEnd::Included) { "<=" } else { "<" };
                    conds.push(format!("{} {} {}", tv.s, op, self.pat_expr(hi, pat)?.at(45)));
                }
                Ok(tmp)
            }
            PatKind::Or(ps) => {
                let mut parts = vec![];
                for p in ps.iter() {
                    let mut c2 = vec![];
                    let mut p2 = vec![];
                    parts.push(self.pat_rec(p, &mut c2, &mut p2, false)?);
                    if !c2.is_empty() || !p2.is_empty() { return unsup("or-pattern with literal sub-patterns or mutable bindings") }
                }
                Ok(format!("({})", parts.join(" | ")))
            }
            PatKind::Ref(p, _, _) | PatKind::Deref(p) => self.pat_rec(p, conds, pro, false),
            PatKind::Slice(before, None, after) if after.is_empty() => {
                let t = Self::peel_refs(self.typeck.pat_ty(pat));
                if !matches!(t.kind(), ty::Slice(_) | ty::Array(..)) { return unsup("slice pattern") }
                let mut parts = vec![];
                for p in before.iter() { parts.push(self.pat_rec(p, conds, pro, false)?); }
                Ok(format!("[{}]", parts.join(", ")))
            }
            PatKind::Slice(..) => unsup("slice pattern with a rest pattern"),
            PatKind::Never => unsup("never pattern"),
            PatKind::Guard(..) => unsup("guard pattern"),
            PatKind::Missing | PatKind::Err(_) => unsup("pattern"),
        }
    }

    fn pat_variant(&mut self, qp: &'tcx hir::QPath<'tcx>, pat: &'tcx hir::Pat<'tcx>) -> R<(DefId, usize)> {
        let t = Self::peel_refs(self.typeck.pat_ty(pat));
        let ty::Adt(def, _) = t.kind() else { return unsup("constructor pattern on non-ADT") };
        let res = self.typeck.qpath_res(qp, pat.hir_id);
        let v = def.variant_of_res(res);
        let vidx = def.variants().iter().position(|x| x.def_id == v.def_id).unwrap_or(0);
        Ok((def.did(), vidx))
    }

    fn ctor_pat(&mut self, adt: DefId, vidx: usize, parts: Vec<String>) -> R<String> {
        let name = match self.fe.std_adt(adt) {
            Some("Option") | Some("Result") | Some("Ordering") => self.tcx.adt_def(adt).variant(vidx.into()).name.to_string(),
            Some("Box") => return parts.into_iter().next().ok_or(Unsup("box pattern".into())),
            Some(_) => return unsup("pattern on a standard library type"),
            None if !adt.is_local() => return unsup("pattern on an external type"),
            None => self.fe.variant_ctor_name(adt, vidx),
        };
        if parts.is_empty() { Ok(name) } else { Ok(format!("{}({})", name, parts.join(", "))) }
    }

    // ------------------------------------------------------------------
    // Closures
    // ------------------------------------------------------------------

    fn closure(&mut self, e: &'tcx hir::Expr<'tcx>, c: &'tcx hir::Closure<'tcx>) -> R<Tr> {
        if !matches!(c.kind, hir::ClosureKind::Closure) { return unsup("async block / coroutine") }
        if let ty::Closure(_, args) = self.ty_of(e).kind() {
            if args.as_closure().kind() == ty::ClosureKind::FnMut {
                return unsup("closure that mutates captured variables");
            }
        }
        let body = self.tcx.hir_body(c.body);
        let mut ps = vec![];
        let mut pro = vec![];
        for (i, p) in body.params.iter().enumerate() {
            match p.pat.kind {
                PatKind::Binding(hir::BindingMode(hir::ByRef::No, m), hid, ident, None) => {
                    let n = names::local_name(ident.as_str());
                    if m.is_mut() {
                        let t = self.typeck.node_type(hid);
                        self.alloc(t, p.pat.span)?;
                        pro.push(format!("let mut {} = {};", n, n));
                        self.locals.insert(hid, Local { name: n.clone(), cell: true });
                    } else {
                        self.locals.insert(hid, Local { name: n.clone(), cell: false });
                    }
                    ps.push(n);
                }
                _ => {
                    let n = format!("carg_{}", i);
                    pro.extend(self.irrefutable(p.pat, &Tr::atom(n.clone()))?);
                    ps.push(n);
                }
            }
        }
        let mut b = pro.join("\n");
        if !b.is_empty() { b.push('\n'); }
        b.push_str(&self.block_expr_inner(body.value)?);
        let head = if ps.is_empty() { "||".to_string() } else { format!("|{}|", ps.join(", ")) };
        Ok(Tr::new(format!("{} {{\n{}\n}}", head, b), 10))
    }
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

fn label_name(s: &str) -> String {
    let s = s.trim_start_matches('\'');
    format!("'{}", names::ident_chars(s))
}

fn hol_char(c: char) -> R<String> {
    if !c.is_ascii() { return unsup("non-ASCII character literal") }
    if c.is_ascii_alphanumeric() || " !#$%&()*+,-./:;<=>?@[]^_`{|}~".contains(c) {
        Ok(format!("CHR ''{}''", c))
    } else {
        Ok(format!("CHR 0x{:02X}", c as u32))
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
fn join_seq(parts: Vec<String>, last_is_let: bool) -> String {
    let mut out = String::new();
    let n = parts.len();
    for (i, p) in parts.into_iter().enumerate() {
        let last = i + 1 == n;
        if let Some(t) = p.strip_prefix('\u{3}') {
            out.push_str(t);
        } else if let Some(t) = p.strip_prefix('\u{4}') {
            out.push_str(t);
            if !last { out.push('\n'); }
        } else if last && last_is_let {
            out.push_str(&p);
        } else {
            // statements already carry a trailing ';'
            out.push_str(&p);
            if !last { out.push('\n'); }
        }
    }
    let _ = paren_ty;
    out
}
