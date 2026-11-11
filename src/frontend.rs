//! Crate-level state of the translation: names, type mapping, collected items.

use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TypeFoldable, TypeVisitableExt};
use rustc_span::{Span, Symbol, sym};

use crate::names;

/// A translated function: a local item with a body, either translated once for all its generic
/// arguments (`None`: type parameters become type variables) or an instance for concrete generic
/// arguments (`Some`: monomorphisation).
pub type FnKey<'tcx> = (DefId, Option<GenericArgsRef<'tcx>>);

/// Instances of one generic function at most; more (e.g. polymorphic recursion) are not translated.
pub const MAX_INSTANCES: usize = 16;

/// Insertion-ordered set of functions (DefId is not `Ord`).
#[derive(Default, Clone)]
pub struct DefSet<'tcx>(pub Vec<FnKey<'tcx>>);
impl<'tcx> DefSet<'tcx> {
    pub fn insert(&mut self, d: FnKey<'tcx>) {
        if !self.0.contains(&d) {
            self.0.push(d)
        }
    }
    pub fn contains(&self, d: &FnKey<'tcx>) -> bool { self.0.contains(d) }
    pub fn iter(&self) -> std::slice::Iter<'_, FnKey<'tcx>> { self.0.iter() }
    pub fn clear(&mut self) { self.0.clear() }
}

/// A placeholder or external type, declared in the types template.
#[derive(Clone)]
pub struct ExtType {
    pub arity: usize,
    pub comment: String,
    /// the constructors of an enum without type arguments whose variants have no fields: the
    /// type is declared as a datatype with these constructors
    pub ctors: Vec<String>,
}

/// An external (or foreign) function for which a template definition is emitted.
pub struct ExtFun {
    pub hol_name: String,
    pub rust_path: String,
    pub hol_type: String,
    pub arity: usize,
}

/// A translated local function (or constant thunk).
pub struct FunDef<'tcx> {
    pub key: FnKey<'tcx>,
    pub name: String,
    pub rust_path: String,
    /// HOL types of the parameters and of the result value.
    pub param_tys: Vec<String>,
    pub ret_ty: String,
    pub params: Vec<String>,
    /// Body (uRust, may contain call markers).
    pub body: String,
    pub calls: DefSet<'tcx>,
    pub comments: Vec<String>,
}

pub struct Frontend<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    names: HashMap<DefId, String>,
    used_names: HashSet<String>,
    type_names: HashMap<DefId, String>,
    used_type_names: HashSet<String>,
    pub ext_types: BTreeMap<String, ExtType>,
    pub ext_funs: BTreeMap<String, ExtFun>,
    ext_fun_ids: HashMap<DefId, String>,
    ext_type_ids: HashMap<DefId, String>,
    pub foreign_funs: BTreeMap<String, ExtFun>,
    pub alloc_types: Vec<String>,
    /// the function items whose types `ty` is translating (a function item's signature may
    /// contain its own type, through an `impl Trait` result)
    fn_items: Vec<DefId>,
    /// the `impl Trait` types whose hidden types `ty` is translating
    opaques: Vec<DefId>,
    pub placeholders: Vec<String>,
    /// Number of uses of placeholder types so far (see `ty_modelled`).
    placeholder_type_uses: usize,
    pub fun_defs: Vec<FunDef<'tcx>>,
    pub item_comments: Vec<String>,
    /// Table used by call markers (`\u{1}C<n>\u{2}` etc.).
    pub marker_ids: Vec<FnKey<'tcx>>,
    marker_index: HashMap<FnKey<'tcx>, usize>,
    /// Generic functions translated per instance: those whose body calls a trait method (or a
    /// generic `Fn` argument) depending on their type parameters, directly or through other such
    /// functions; trait default methods (generic over `Self`).
    pub mono_fns: HashSet<DefId>,
    instance_names: HashMap<(DefId, GenericArgsRef<'tcx>), String>,
    instances_per_fn: HashMap<DefId, usize>,
    /// Instances named but not yet translated.
    pub pending: Vec<FnKey<'tcx>>,
    /// Local ADTs that no HOL datatype expresses, with the reason: they recur with other type
    /// arguments than their own parameters (e.g. `enum E<A, B> { V(Box<E<B, A>>) }`), or have no
    /// finite values once shared references are values (e.g. `struct Node(&'static Node)`), or
    /// are in a recursive group with such a type. They are placeholders.
    pub opaque_adts: HashMap<DefId, &'static str>,
    /// Structs translated as `datatype_record` (have lenses).
    pub record_adts: HashSet<DefId>,
    /// Local ADTs that contain `&mut` references (directly or through other ADTs):
    /// they take the type parameters `'addr, 'gv` first.
    pub ref_adts: HashSet<DefId>,
    /// When set, unnormalisable projections and `impl Trait` become fresh type variables.
    pub alias_tvars: Option<usize>,
    /// For a local ADT whose fields mention associated types of its type parameters (e.g.
    /// `struct H<S: Shape> { u: S::Unit }`), these projections in order: each is an extra type
    /// parameter of its datatype, instantiated at a use `H<Sq>` by the normalised `<Sq as Shape>::Unit`.
    pub adt_projs: HashMap<DefId, Vec<Ty<'tcx>>>,
    /// While a datatype is declared: its projections' type variables (see `adt_projs`).
    pub proj_tvars: Option<HashMap<ty::AliasTy<'tcx>, String>>,
}

/// The type of field `f` of an ADT at its type arguments `args`, without regions and normalised in
/// `env`. A field is this type wherever the frontend looks at it, as in Rust: a projection is the
/// type it denotes (`<Foo as Tr>::Out` is `Bar`), and what remains of one depends on type parameters.
pub fn field_ty<'tcx>(tcx: TyCtxt<'tcx>, f: &ty::FieldDef, args: GenericArgsRef<'tcx>, env: ty::TypingEnv<'tcx>) -> Ty<'tcx> {
    tcx.erase_and_anonymize_regions(tcx.normalize_erasing_regions(env, f.ty(tcx, args)))
}

pub fn paren_ty(s: &str) -> String {
    if s.contains(' ') && !(s.starts_with('(') && balanced_outer(s)) { format!("({})", s) } else { s.to_string() }
}

fn balanced_outer(s: &str) -> bool {
    // true if s is "( ... )" with the outer parentheses matching each other
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        if c == '(' { depth += 1 }
        if c == ')' {
            depth -= 1;
            if depth == 0 && i != s.len() - 1 { return false }
        }
    }
    true
}

impl<'tcx> Frontend<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Frontend {
            tcx,
            names: HashMap::new(),
            used_names: HashSet::new(),
            type_names: HashMap::new(),
            used_type_names: HashSet::new(),
            ext_types: BTreeMap::new(),
            ext_funs: BTreeMap::new(),
            ext_fun_ids: HashMap::new(),
            ext_type_ids: HashMap::new(),
            foreign_funs: BTreeMap::new(),
            alloc_types: Vec::new(),
            fn_items: Vec::new(),
            opaques: Vec::new(),
            placeholders: Vec::new(),
            placeholder_type_uses: 0,
            fun_defs: Vec::new(),
            item_comments: Vec::new(),
            marker_ids: Vec::new(),
            marker_index: HashMap::new(),
            mono_fns: HashSet::new(),
            instance_names: HashMap::new(),
            instances_per_fn: HashMap::new(),
            pending: Vec::new(),
            opaque_adts: HashMap::new(),
            record_adts: HashSet::new(),
            ref_adts: HashSet::new(),
            alias_tvars: None,
            adt_projs: HashMap::new(),
            proj_tvars: None,
        }
    }

    pub fn snippet(&self, sp: Span) -> String {
        self.tcx.sess.source_map().span_to_snippet(sp).unwrap_or_else(|_| "?".to_string())
    }

    /// Record a placeholder for the unsupported feature `what` at `sp` (if known). Returns the
    /// text that marks it in the generated theories, in a term or in a comment.
    pub fn placeholder(&mut self, what: &str, sp: Option<Span>) -> String {
        let marker = match sp {
            Some(sp) => format!("PLACEHOLDER {}: {}", what, one_line(&self.snippet(sp))),
            None => format!("PLACEHOLDER {}", what),
        };
        let loc = sp.map(|sp| format!("line {}: ", self.tcx.sess.source_map().lookup_char_pos(sp.lo()).line)).unwrap_or_default();
        self.placeholders.push(format!("{}{}", loc, marker));
        marker
    }

    /// Record a placeholder for an item (outside any function body): it is listed in the
    /// comments at the head of the functions theory.
    pub fn item_placeholder(&mut self, what: &str, sp: Span) {
        let m = self.placeholder(what, Some(sp));
        self.item_comments.push(m);
    }

    pub fn marker(&mut self, key: FnKey<'tcx>) -> usize {
        if let Some(i) = self.marker_index.get(&key) { return *i }
        let i = self.marker_ids.len();
        self.marker_ids.push(key);
        self.marker_index.insert(key, i);
        i
    }

    /// `x` (from the type-checking results of a generic body) at the concrete generic arguments
    /// `args`, with projections normalised.
    pub fn mono<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(&self, args: GenericArgsRef<'tcx>, x: T) -> T {
        let x = ty::EarlyBinder::bind(self.tcx, x).instantiate(self.tcx, args);
        match self.tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), x) {
            Ok(n) => n,
            Err(_) => x.skip_normalization(),
        }
    }

    /// The function to call for the local item `did` at the generic arguments `args`: an instance
    /// (queued for translation) if `did` is translated per instance and `args` are concrete,
    /// otherwise the item itself. `None` if `did` already has `MAX_INSTANCES` instances.
    pub fn callee(&mut self, did: DefId, args: GenericArgsRef<'tcx>) -> Option<FnKey<'tcx>> {
        // an instance at a type without a uRust model (e.g. a closure type) could not be
        // translated; the generic function, whose type variable it instantiates, is called instead
        if !self.mono_fns.contains(&did) || args.has_param() || !args.types().all(|t| self.ty_dry(t).1) {
            return Some((did, None));
        }
        let args = self.tcx.erase_and_anonymize_regions(args);
        if !self.instance_names.contains_key(&(did, args)) {
            let count = self.instances_per_fn.entry(did).or_insert(0);
            if *count >= MAX_INSTANCES {
                return None;
            }
            *count += 1;
            let mut segs = self.path_segments(did);
            segs.extend(args.types().map(|t| self.short_ty_name(t)));
            let n = unique(names::global_name(&segs), |n| self.used_names.contains(n));
            self.used_names.insert(n.clone());
            self.instance_names.insert((did, args), n);
            self.pending.push((did, Some(args)));
        }
        Some((did, Some(args)))
    }

    /// HOL name of a function (`def_name` of the item, or the name of the instance).
    pub fn fn_name(&mut self, key: FnKey<'tcx>) -> String {
        match key.1 {
            None => self.def_name(key.0),
            Some(args) => self.instance_names[&(key.0, args)].clone(),
        }
    }

    // ------------------------------------------------------------------
    // Paths and names
    // ------------------------------------------------------------------

    /// Crate-relative path segments; `impl` segments are replaced by the
    /// name of the self type (and the trait, for trait impls).
    pub fn path_segments(&self, did: DefId) -> Vec<String> {
        let key = self.tcx.def_key(did);
        let parent = key.parent.map(|p| DefId { krate: did.krate, index: p });
        let mut segs = match parent { Some(p) => self.path_segments(p), None => vec![] };
        match key.disambiguated_data.data {
            DefPathData::CrateRoot => {}
            DefPathData::Impl => {
                segs.extend(self.impl_segments(did));
            }
            DefPathData::Ctor => {}
            DefPathData::Closure => segs.push("closure".to_string()),
            _ => {
                // unnamed segments (extern blocks, anonymous consts, ...) are dropped
                if let Some(sym) = key.disambiguated_data.data.get_opt_name() {
                    segs.push(sym.to_string());
                }
            }
        }
        segs
    }

    fn impl_segments(&self, impl_did: DefId) -> Vec<String> {
        let self_ty = self.tcx.type_of(impl_did).instantiate_identity().skip_normalization();
        let mut v = vec![self.short_ty_name(self_ty)];
        if let Some(tr) = self.tcx.impl_opt_trait_ref(impl_did) {
            v.push(self.tcx.item_name(tr.skip_binder().def_id).to_string());
        }
        v
    }

    pub fn short_ty_name(&self, t: Ty<'tcx>) -> String {
        match t.kind() {
            ty::Adt(def, _) => self.tcx.item_name(def.did()).to_string(),
            ty::Ref(_, inner, _) => self.short_ty_name(*inner),
            ty::Slice(_) => "slice".into(),
            ty::Array(..) => "array".into(),
            ty::Str => "str".into(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => format!("{}", t),
            ty::Tuple(_) => "tuple".into(),
            ty::Param(p) => p.name.to_string(),
            _ => "impl".into(),
        }
    }

    /// HOL constant name of a local item (function, const, static).
    pub fn def_name(&mut self, did: DefId) -> String {
        if let Some(n) = self.names.get(&did) { return n.clone() }
        let n = unique(names::global_name(&self.path_segments(did)), |n| self.used_names.contains(n));
        self.used_names.insert(n.clone());
        self.names.insert(did, n.clone());
        n
    }

    /// HOL type name of a local ADT.
    pub fn adt_name(&mut self, did: DefId) -> String {
        if let Some(n) = self.type_names.get(&did) { return n.clone() }
        let n = unique(names::type_name(&self.path_segments(did)), |n| {
            self.used_type_names.contains(n) || self.used_names.contains(n)
        });
        self.used_type_names.insert(n.clone());
        // constructor function / notation names derive from the type name
        self.used_names.insert(n.clone());
        self.type_names.insert(did, n.clone());
        n
    }

    pub fn variant_ctor_name(&mut self, adt: DefId, vidx: usize) -> String {
        let tn = self.adt_name(adt);
        let def = self.tcx.adt_def(adt);
        let n = if def.is_enum() {
            let v = def.variant(vidx.into());
            format!("{}_{}", tn, names::ident_chars(v.name.as_str()))
        } else {
            format!("make_{}", tn)
        };
        self.used_names.insert(n.clone());
        self.used_names.insert(format!("{}_mk", n));
        n
    }

    /// HOL name of the constructor *function* (`X_mk`, `X_V_mk`) called from uRust.
    pub fn variant_call_name(&mut self, adt: DefId, vidx: usize) -> String {
        let tn = self.adt_name(adt);
        let def = self.tcx.adt_def(adt);
        if def.is_enum() { format!("{}_mk", self.variant_ctor_name(adt, vidx)) } else { format!("{}_mk", tn) }
    }

    pub fn field_name(&mut self, adt: DefId, vidx: usize, fidx: usize) -> String {
        let tn = self.adt_name(adt);
        let def = self.tcx.adt_def(adt);
        let v = def.variant(vidx.into());
        let f: &ty::FieldDef = v.fields.iter().nth(fidx).unwrap();
        let fname = f.name.as_str();
        let n = if def.is_enum() {
            format!("{}_{}_{}", tn, names::ident_chars(v.name.as_str()), names::ident_chars(fname))
        } else {
            format!("{}_{}", tn, names::ident_chars(fname))
        };
        // selectors are HOL constants: functions must not reuse their names
        self.used_names.insert(n.clone());
        n
    }

    pub fn crate_of(&self, did: DefId) -> String {
        self.tcx.crate_name(did.krate).to_string()
    }

    /// Is `did` an item of the standard library? Its crates are those the compiler itself refers to
    /// by these symbols (the injected `extern crate std` / `core`).
    pub fn is_std(&self, did: DefId) -> bool {
        matches!(self.tcx.crate_name(did.krate), sym::core | sym::alloc | sym::std)
    }

    /// The standard library ADTs with a uRust counterpart, recognised by their lang or
    /// diagnostic item.
    pub fn std_adt(&self, did: DefId) -> Option<&'static str> {
        let tcx = self.tcx;
        let lang = |item| tcx.is_lang_item(did, item);
        let diag = |name| tcx.is_diagnostic_item(name, did);
        Some(if lang(LangItem::Option) {
            "Option"
        } else if diag(sym::Result) {
            "Result"
        } else if lang(LangItem::OwnedBox) {
            "Box"
        } else if diag(sym::Vec) {
            "Vec"
        } else if lang(LangItem::String) {
            "String"
        } else if lang(LangItem::OrderingEnum) {
            "Ordering"
        } else if lang(LangItem::Range) {
            "Range"
        } else if lang(LangItem::RangeInclusiveStruct) {
            "RangeInclusive"
        } else if diag(Symbol::intern("Formatter")) {
            "Formatter"
        } else if Some(did) == self.fmt_error() {
            "FmtError"
        } else {
            return None;
        })
    }

    /// `core::fmt::Error`: the error type of the result of `Display::fmt`.
    pub fn fmt_error(&self) -> Option<DefId> {
        let tcx = self.tcx;
        let display = tcx.get_diagnostic_item(sym::Display)?;
        let fmt = tcx.associated_items(display).in_definition_order().find(|i| i.is_fn())?.def_id;
        match tcx.fn_sig(fmt).skip_binder().output().skip_binder().kind() {
            ty::Adt(_, args) => match args.type_at(1).kind() {
                ty::Adt(e, _) => Some(e.did()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Does a value of type `t` have interior mutability, i.e. does it contain an `UnsafeCell`
    /// that is not behind a pointer? Fields are followed with the actual type arguments; type
    /// parameters and projections count as having none.
    pub fn interior_mutable(&self, t: Ty<'tcx>, env: ty::TypingEnv<'tcx>) -> bool {
        self.has_cell(t, env, &mut vec![])
    }

    fn has_cell(&self, t: Ty<'tcx>, env: ty::TypingEnv<'tcx>, seen: &mut Vec<Ty<'tcx>>) -> bool {
        let tcx = self.tcx;
        match t.kind() {
            ty::Adt(def, _) if def.is_box() => false,
            ty::Adt(def, args) => {
                if tcx.is_lang_item(def.did(), LangItem::UnsafeCell) {
                    return true;
                }
                if seen.contains(&t) {
                    return false;
                }
                seen.push(t);
                def.all_fields().any(|f| self.has_cell(field_ty(tcx, f, args, env), env, seen))
            }
            ty::Tuple(ts) => ts.iter().any(|a| self.has_cell(a, env, seen)),
            ty::Array(a, _) | ty::Slice(a) => self.has_cell(*a, env, seen),
            _ => false,
        }
    }

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    pub fn placeholder_type(&mut self, desc: &str, arity: usize) -> String {
        self.placeholder_type_uses += 1;
        let name = format!("unsupported_{}", names::ident_chars(desc));
        if !self.ext_types.contains_key(&name) {
            let comment = self.placeholder(&format!("type {}", desc), None);
            self.ext_types.insert(name.clone(), ExtType { arity, comment, ctors: vec![] });
        }
        name
    }

    /// Map a Rust type to a HOL type; also tells whether every part of it has a uRust model
    /// (no placeholder type was used).
    pub fn ty_modelled(&mut self, t: Ty<'tcx>) -> (String, bool) {
        let before = self.placeholder_type_uses;
        let h = self.ty(t);
        (h, self.placeholder_type_uses == before)
    }

    /// `ty_modelled` without recording anything (placeholder or external types).
    pub fn ty_dry(&mut self, t: Ty<'tcx>) -> (String, bool) {
        let placeholders = self.placeholders.len();
        let ext_types = self.ext_types.clone();
        let ext_type_ids = self.ext_type_ids.clone();
        let r = self.ty_modelled(t);
        self.placeholders.truncate(placeholders);
        self.ext_types = ext_types;
        self.ext_type_ids = ext_type_ids;
        r
    }

    /// Does the HOL type of `t` (see `ty`) have a finite value? `&T`, `Box<T>`, ranges of `T` and
    /// tuples have one iff their parts do, `Result<A, B>` iff `A` or `B` does, a local ADT of
    /// `local` iff some variant's fields do (at its type arguments); lists, options, `&mut`
    /// references, type variables and abstract types always have one. `stack` holds the local
    /// ADTs being decided: a value of one of them inside itself is not finite (least fixpoint).
    /// `known` holds local ADTs found to have a finite value (which does not depend on `stack`).
    /// Fields are normalised in `env`.
    pub fn finite_ty(
        &self,
        t: Ty<'tcx>,
        env: ty::TypingEnv<'tcx>,
        local: &HashSet<DefId>,
        stack: &mut Vec<Ty<'tcx>>,
        known: &mut HashSet<Ty<'tcx>>,
    ) -> bool {
        match t.kind() {
            ty::Ref(_, inner, m) if !m.is_mut() => self.finite_ty(*inner, env, local, stack, known),
            ty::Tuple(ts) => ts.iter().all(|x| self.finite_ty(x, env, local, stack, known)),
            ty::Adt(def, args) if local.contains(&def.did()) => {
                if self.opaque_adts.contains_key(&def.did()) || (def.is_enum() && def.variants().is_empty()) {
                    return true;
                }
                if known.contains(&t) {
                    return true;
                }
                if stack.contains(&t) {
                    return false;
                }
                stack.push(t);
                let r = def.variants().iter().any(|v| {
                    v.fields.iter().all(|f| self.finite_ty(field_ty(self.tcx, f, args, env), env, local, stack, known))
                });
                stack.pop();
                if r {
                    known.insert(t);
                }
                r
            }
            ty::Adt(def, args) => match self.std_adt(def.did()) {
                Some("Box") | Some("Range") | Some("RangeInclusive") => self.finite_ty(args.type_at(0), env, local, stack, known),
                Some("Result") => {
                    self.finite_ty(args.type_at(0), env, local, stack, known)
                        || self.finite_ty(args.type_at(1), env, local, stack, known)
                }
                _ => true,
            },
            _ => true,
        }
    }

    /// The associated types of type parameters in the types `tys` (normalised in `did`'s typing
    /// environment), in order of occurrence: those written, and those the datatypes of local ADTs
    /// in them take as extra type parameters (see `adt_projs`).
    pub fn projections(&self, did: DefId, tys: &[Ty<'tcx>]) -> Vec<Ty<'tcx>> {
        let env = ty::TypingEnv::post_analysis(self.tcx, did);
        let mut out: Vec<Ty<'tcx>> = vec![];
        let add = |p: Ty<'tcx>, out: &mut Vec<Ty<'tcx>>| {
            if let ty::Alias(_, a) = p.kind()
                && p.has_param()
                && !out.iter().any(|q| matches!(q.kind(), ty::Alias(_, b) if b == a))
            {
                out.push(p);
            }
        };
        for &t in tys {
            let mut w = self.tcx.erase_and_anonymize_regions(t).walk();
            while let Some(g) = w.next() {
                let ty::GenericArgKind::Type(x) = g.kind() else { continue };
                match x.kind() {
                    ty::Alias(..) => {
                        w.skip_current_subtree();
                        add(x, &mut out);
                    }
                    ty::Adt(def, args) => {
                        for &p in self.adt_projs.get(&def.did()).into_iter().flatten() {
                            let at = ty::EarlyBinder::bind(self.tcx, p).instantiate(self.tcx, *args);
                            add(self.tcx.try_normalize_erasing_regions(env, at).unwrap_or(at.skip_normalization()), &mut out);
                        }
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// Map a Rust type to a HOL type.
    pub fn ty(&mut self, t: Ty<'tcx>) -> String {
        match t.kind() {
            ty::Bool => "bool".into(),
            ty::Char => "char".into(),
            ty::Int(it) => match it {
                ty::IntTy::I8 => "8 sword".into(),
                ty::IntTy::I16 => "16 sword".into(),
                ty::IntTy::I32 => "32 sword".into(),
                ty::IntTy::I64 | ty::IntTy::Isize => "64 sword".into(),
                ty::IntTy::I128 => self.placeholder_type("i128", 0),
            },
            ty::Uint(ut) => match ut {
                ty::UintTy::U8 => "8 word".into(),
                ty::UintTy::U16 => "16 word".into(),
                ty::UintTy::U32 => "32 word".into(),
                ty::UintTy::U64 | ty::UintTy::Usize => "64 word".into(),
                ty::UintTy::U128 => self.placeholder_type("u128", 0),
            },
            ty::Float(ft) => self.placeholder_type(&format!("{:?}", ft).to_lowercase(), 0),
            ty::Str => "String.literal".into(),
            ty::Ref(_, inner, m) => {
                let i = self.ty(*inner);
                if m.is_mut() { format!("('addr, 'gv, {}) Global_Store.ref", i) } else { i }
            }
            ty::Slice(inner) => format!("{} list", paren_ty(&self.ty(*inner))),
            ty::Array(inner, _) => format!("{} list", paren_ty(&self.ty(*inner))),
            ty::Tuple(ts) => {
                if ts.is_empty() {
                    "unit".into()
                } else {
                    let parts: Vec<String> = ts.iter().map(|x| paren_ty(&self.ty(x))).collect();
                    format!("({} \\<times> tnil)", parts.join(" \\<times> "))
                }
            }
            ty::Never => "unit".into(),
            ty::Param(p) => names::tvar_name(p.name.as_str()),
            ty::Adt(def, args) => {
                let did = def.did();
                let targs: Vec<Ty<'tcx>> = args.types().collect();
                match self.std_adt(did) {
                    Some("Option") => format!("{} option", paren_ty(&self.ty(targs[0]))),
                    Some("Result") => {
                        let a = self.ty(targs[0]);
                        let b = self.ty(targs[1]);
                        format!("({}, {}) result", a, b)
                    }
                    Some("Box") => self.ty(targs[0]),
                    Some("Vec") => format!("{} list", paren_ty(&self.ty(targs[0]))),
                    Some("String") => "String.literal".into(),
                    Some("Ordering") => "ordering".into(),
                    // AutoCorrode's model of `core::fmt` (`StdLib_Fmt`)
                    Some("Formatter") => "fmt_Formatter".into(),
                    Some("FmtError") => "fmt_Error".into(),
                    Some("Range") | Some("RangeInclusive") => {
                        format!("{} range", paren_ty(&self.ty(targs[0])))
                    }
                    _ => {
                        let name = if let Some(&why) = self.opaque_adts.get(&did) {
                            let n = self.tcx.def_path_str(did);
                            self.placeholder_type(&format!("{} {}", why, n), targs.len())
                        } else if did.is_local() && !def.is_union() {
                            self.adt_name(did)
                        } else if did.is_local() {
                            self.placeholder_type(&format!("union {}", self.tcx.def_path_str(did)), targs.len())
                        } else {
                            self.ext_type(did, targs.len())
                        };
                        let mut a: Vec<String> = vec![];
                        if self.ref_adts.contains(&did) && !self.opaque_adts.contains_key(&did) {
                            a.push("'addr".into());
                            a.push("'gv".into());
                        }
                        a.extend(targs.iter().map(|x| self.ty(*x)));
                        // a placeholder ADT is declared with the Rust type arguments only
                        if let Some(ps) = self.adt_projs.get(&did).cloned().filter(|_| !self.opaque_adts.contains_key(&did)) {
                            for p in ps {
                                let at = ty::EarlyBinder::bind(self.tcx, p).instantiate(self.tcx, *args).skip_normalization();
                                a.push(self.ty(at));
                            }
                        }
                        if a.is_empty() { name } else { format!("({}) {}", a.join(", "), name) }
                    }
                }
            }
            ty::RawPtr(..) => self.placeholder_type("raw_pointer", 0),
            ty::FnPtr(..) => self.placeholder_type("fn_pointer", 0),
            ty::Dynamic(..) => self.placeholder_type("dyn_trait", 0),
            ty::Alias(..) => {
                // associated-type projections that can be resolved (e.g. `<V2 as Add>::Output`); lifetime
                // parameters do not matter (HOL has no regions), so they are erased first
                let t = self.tcx.erase_and_anonymize_regions(t);
                if let ty::Alias(_, a) = t.kind() && let Some(v) = self.proj_tvars.as_ref().and_then(|m| m.get(a)) {
                    return v.clone();
                }
                if !t.has_escaping_bound_vars() && !t.has_param() && let Ok(n) = self.tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), rustc_middle::ty::Unnormalized::new_wip(t)) {
                    if !matches!(n.kind(), ty::Alias(..)) {
                        return self.ty(n);
                    }
                }
                // an `impl Trait` type is its hidden type (as the compiler reveals it after type
                // checking), also in generic code; one containing itself stays a placeholder
                if let ty::Alias(_, a) = t.kind()
                    && let ty::AliasTyKind::Opaque { def_id } = a.kind
                    && !self.opaques.contains(&def_id)
                {
                    let hidden = ty::EarlyBinder::bind(self.tcx, self.tcx.type_of(def_id).instantiate_identity().skip_normalization())
                        .instantiate(self.tcx, a.args)
                        .skip_normalization();
                    self.opaques.push(def_id);
                    let h = self.ty(hidden);
                    self.opaques.pop();
                    return h;
                }
                match self.alias_tvars.as_mut() {
                    Some(k) => {
                        *k += 1;
                        format!("'alias{}", k)
                    }
                    None => self.placeholder_type("alias_or_impl_trait", 0),
                }
            }
            // a uRust closure `|x, y| e` is `λx y. FunctionBody e`: a function of its formals
            ty::Closure(_, args) => {
                let sig = self.tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
                let formals: Vec<Ty<'tcx>> = match sig.inputs()[0].kind() {
                    ty::Tuple(ts) => ts.iter().collect(),
                    _ => vec![sig.inputs()[0]],
                };
                let params: Vec<String> = formals.iter().map(|t| self.ty(*t)).collect();
                let ret = self.ty(sig.output());
                self.fun_type(&params, &ret)
            }
            // a function item is used as the closure calling it (see `BodyTr::fn_item_value`)
            ty::FnDef(did, _) => {
                if self.fn_items.contains(did) { return self.placeholder_type("recursive fn_item", 0) }
                self.fn_items.push(*did);
                let sig = self.tcx.instantiate_bound_regions_with_erased(t.fn_sig(self.tcx));
                let params: Vec<String> = sig.inputs().iter().map(|t| self.ty(*t)).collect();
                let ret = self.ty(sig.output());
                self.fn_items.pop();
                self.fun_type(&params, &ret)
            }
            _ => self.placeholder_type(&format!("{}", t), 0),
        }
    }

    pub fn fun_type(&self, param_tys: &[String], ret: &str) -> String {
        let mut s = String::new();
        for p in param_tys {
            s.push_str(&paren_ty(p));
            s.push_str(" \\<Rightarrow> ");
        }
        s.push_str(&format!("('s, {}, 'abort, 'i prompt, 'o prompt_output) function_body", ret));
        s
    }

    pub fn need_alloc(&mut self, hol_ty: &str) {
        if !self.alloc_types.iter().any(|t| t == hol_ty) {
            self.alloc_types.push(hol_ty.to_string());
        }
    }

    /// Register (or look up) an external ADT with `arity` type arguments, returning its HOL name,
    /// made of its full path: items of different modules may share a name.
    fn ext_type(&mut self, did: DefId, arity: usize) -> String {
        if let Some(n) = self.ext_type_ids.get(&did) { return n.clone() }
        let mut segs = vec![self.crate_of(did)];
        segs.extend(self.path_segments(did));
        let n = unique(format!("ext_{}", names::ident_chars(&segs.join("_"))), |n| {
            self.ext_types.contains_key(n) || self.used_type_names.contains(n)
        });
        let ctors = match self.tcx.def_kind(did) {
            DefKind::Enum if arity == 0 => {
                let def = self.tcx.adt_def(did);
                if !def.variants().is_empty() && def.variants().iter().all(|v| v.fields.is_empty()) {
                    def.variants().iter().map(|v| format!("{}_{}", n, names::ident_chars(v.name.as_str()))).collect()
                } else {
                    vec![]
                }
            }
            _ => vec![],
        };
        self.ext_types.insert(n.clone(), ExtType { arity, comment: format!("Rust: {}", self.tcx.def_path_str(did)), ctors });
        self.ext_type_ids.insert(did, n.clone());
        n
    }

    /// The constructor of the variant `vidx` of the external enum `adt` when it is declared with
    /// its constructors (see `ExtType::ctors`).
    pub fn ext_ctor(&mut self, adt: DefId, vidx: usize) -> Option<String> {
        if self.tcx.def_kind(adt) != DefKind::Enum { return None }
        let arity = self.tcx.generics_of(adt).own_counts().types;
        let n = self.ext_type(adt, arity);
        self.ext_types.get(&n).and_then(|t| t.ctors.get(vidx).cloned())
    }

    // ------------------------------------------------------------------
    // External functions
    // ------------------------------------------------------------------

    /// Register (or look up) an external function, returning its HOL name.
    pub fn ext_fun(&mut self, did: DefId, foreign: bool) -> String {
        if let Some(n) = self.ext_fun_ids.get(&did) { return n.clone() }
        let mut segs = vec![];
        if !did.is_local() { segs.push(self.crate_of(did)); }
        segs.extend(self.path_segments(did));
        let base = format!("{}{}", if foreign { "" } else { "ext_" }, names::global_name(&segs));
        let n = unique(base, |n| self.used_names.contains(n));
        self.used_names.insert(n.clone());
        let sig = self.tcx.fn_sig(did).instantiate_identity().skip_binder();
        self.alias_tvars = Some(0);
        let params: Vec<String> = sig.inputs().iter().map(|t| self.ty(*t)).collect();
        let ret = self.ty(sig.output());
        self.alias_tvars = None;
        let hol_type = self.fun_type(&params, &ret);
        let ef = ExtFun { hol_name: n.clone(), rust_path: self.tcx.def_path_str(did), hol_type, arity: params.len() };
        if foreign { self.foreign_funs.insert(n.clone(), ef); } else { self.ext_funs.insert(n.clone(), ef); }
        self.ext_fun_ids.insert(did, n.clone());
        n
    }

    // ------------------------------------------------------------------
    // Item collection
    // ------------------------------------------------------------------

    pub fn local_fn_with_body(&self, did: DefId) -> bool {
        let Some(ld) = did.as_local() else { return false };
        matches!(self.tcx.def_kind(did), DefKind::Fn | DefKind::AssocFn)
            && self.tcx.hir_maybe_body_owned_by(ld).is_some()
            && !self.bodiless_intrinsic(did)
    }

    /// A local intrinsic declared without a body (rustc gives it a placeholder body): it is
    /// external, like a function of another crate.
    pub fn bodiless_intrinsic(&self, did: DefId) -> bool {
        self.tcx.intrinsic(did).is_some_and(|i| i.must_be_overridden)
    }

    pub fn is_trait_item(&self, did: DefId) -> bool {
        matches!(self.tcx.def_kind(self.tcx.parent(did)), DefKind::Trait)
    }
}

/// `base`, or the first of `base_2`, `base_3`, ... that is not `taken`.
fn unique(base: String, taken: impl Fn(&str) -> bool) -> String {
    let mut n = base.clone();
    let mut k = 1;
    while taken(&n) {
        k += 1;
        n = format!("{}_{}", base, k);
    }
    n
}

pub fn one_line(s: &str) -> String {
    let s: String = s.split_whitespace().collect::<Vec<_>>().join(" ");
    if s.len() > 120 { format!("{}...", &s[..s.char_indices().nth(117).map(|x| x.0).unwrap_or(s.len())]) } else { s }
}
