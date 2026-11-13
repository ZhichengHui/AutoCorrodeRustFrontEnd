//! Crate-level state of the translation: names, type mapping, collected items.

use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TypeFoldable, TypeVisitableExt};
use rustc_span::{Span, Symbol, sym};

use crate::names;

/// How a local item with a body is translated.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Inst<'tcx> {
    /// Once for all its generic arguments: type parameters become type variables, trait bounds
    /// dictionary parameters.
    Generic,
    /// An instance at concrete generic arguments (monomorphisation).
    Mono(GenericArgsRef<'tcx>),
    /// A trait default method for an implementation (the `DefId`) that does not override it:
    /// `Self` is the implementing type, generic over the implementation's parameters, whose trait
    /// bounds are its dictionary parameters.
    ImplCopy(DefId),
}

/// A translated function: a local item with a body, and how it is translated.
pub type FnKey<'tcx> = (DefId, Inst<'tcx>);

/// Instances of one generic function at most; more (e.g. polymorphic recursion) are not translated.
pub const MAX_INSTANCES: usize = 64;

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

/// A call (or, without arguments, a function value) of a local generic function in a translated
/// body. Its text is a marker (`\u{1}F<n>\u{2}`, `\u{1}V<n>\u{2}`) completed at emission, when
/// the allocation record the callee takes, if any, is known (see `translate::alloc_sets`).
pub struct GenCall<'tcx> {
    pub callee: FnKey<'tcx>,
    /// the generic arguments of the item the callee's dictionary parameters are the bounds of
    pub kargs: GenericArgsRef<'tcx>,
    /// the callee's dictionaries
    pub dicts: Vec<String>,
    /// the arguments (`None`: the function as a value)
    pub args: Option<Vec<String>>,
}

/// A placeholder or external type, declared in the types template.
#[derive(Clone)]
pub struct ExtType {
    pub arity: usize,
    pub comment: String,
    /// For an enum, or a struct whose fields are all public, whose field types all have uRust
    /// models: its datatype's type parameters (the type parameters, then the associated types
    /// in its fields, see `adt_projs`), and its constructors with their field types. Otherwise
    /// (empty) the type is declared abstractly.
    pub ctors: Vec<(String, Vec<String>)>,
    pub params: Vec<String>,
    /// the external types its fields use
    pub deps: Vec<String>,
    /// for an enum with constructors whose variants have no fields: it is a `simple_word_enum`
    /// (see `Frontend::word_enum`)
    pub word: Option<(u64, Vec<u128>)>,
    /// for an enum with constructors, without type parameters, not in its own fields: it is an
    /// `enum` (Enum_Theory), see `translate::enum_decl`
    pub plain_enum: bool,
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
    /// For a constant translated from its value (see `translate::const_data`): the value as
    /// `urust_const_data` data; `body` is then empty.
    pub data: Option<String>,
    pub calls: DefSet<'tcx>,
    pub comments: Vec<String>,
    /// how many of the parameters are dictionaries (they come first)
    pub n_dicts: usize,
    /// the type variables of projections and the function types of `Fn`-bounded parameters of the
    /// definition (see `Frontend::proj_tvars`, `Frontend::fn_params`)
    pub proj_ctx: Option<HashMap<ty::AliasTy<'tcx>, String>>,
    pub fn_ctx: HashMap<u32, String>,
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
    /// their canonical forms (see `need_alloc`)
    alloc_keys: Vec<String>,
    /// the function items whose types `ty` is translating (a function item's signature may
    /// contain its own type, through an `impl Trait` result)
    fn_items: Vec<DefId>,
    /// `core::fmt::Error` (see `fmt_error_of`)
    fmt_error: Option<DefId>,
    /// the standard library iterators and other ADTs that have models but no lang or diagnostic
    /// item of their own (see `std_adts_of`)
    std_adts: Vec<(DefId, &'static str)>,
    /// the formatting traits: the bounds of the `fmt::rt::Argument` constructors (`Display`,
    /// `Debug`, `LowerHex`, ..., `Pointer`), with their names
    pub fmt_traits: Vec<(DefId, String)>,
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
    /// whether the crate implements `Drop` for a type (see `BodyTr::needs_glue`)
    pub has_drop_impls: bool,
    instance_names: HashMap<(DefId, GenericArgsRef<'tcx>), String>,
    /// names of the copies of default methods, by (method, implementation)
    copy_names: HashMap<(DefId, DefId), String>,
    /// the traits whose dictionaries are used, in order, with their datatypes' names
    pub dict_traits: Vec<DefId>,
    pub dict_names: HashMap<DefId, String>,
    instances_per_fn: HashMap<DefId, usize>,
    /// Instances named but not yet translated.
    pub pending: Vec<FnKey<'tcx>>,
    /// Local ADTs that no HOL datatype expresses, with the reason: they recur with other type
    /// arguments than their own parameters (e.g. `enum E<A, B> { V(Box<E<B, A>>) }`), or have no
    /// finite values once shared references are values (e.g. `struct Node(&'static Node)`), or
    /// are in a recursive group with such a type. They are placeholders.
    pub opaque_adts: HashMap<DefId, &'static str>,
    /// Structs translated as `scalable_datatype_record` (have lenses).
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
    /// While a generic item is translated: its typing environment, in which the associated types a
    /// local ADT takes as type parameters are normalised at its uses (to the projections that
    /// `proj_tvars` has, e.g. `<DP::VS as VersionSet>::V` to `DP::V`).
    pub proj_env: Option<ty::TypingEnv<'tcx>>,
    /// The methods of each trait that are fields of its dictionaries (see `dict_methods`).
    pub dict_methods_memo: std::cell::RefCell<HashMap<DefId, Vec<DefId>>>,
    /// The own bounds of each trait method that are dictionary parameters (see `own_dict_bounds`).
    pub own_dict_bounds_memo: std::cell::RefCell<HashMap<DefId, Vec<ty::TraitRef<'tcx>>>>,
    /// While a generic item is translated: the function types of its type parameters bounded by
    /// `Fn` traits (see `fn_param_types`).
    pub fn_params: HashMap<u32, String>,
    /// The mutable locals of types with generic parameters, by marker index (`\u{1}A<n>\u{2}`):
    /// the translation whose body has one, its type and HOL type (see `BodyTr::alloc`).
    pub alloc_sites: Vec<(FnKey<'tcx>, Ty<'tcx>, String)>,
    /// The calls of local generic functions, by marker index (see `GenCall`).
    pub gen_calls: Vec<GenCall<'tcx>>,
}

/// The type of field `f` of an ADT at its type arguments `args`, without regions and normalised in
/// `env`. A field is this type wherever the frontend looks at it, as in Rust: a projection is the
/// type it denotes (`<Foo as Tr>::Out` is `Bar`), and what remains of one depends on type parameters.
/// Does the type `t` contain a `&mut` reference (outside function pointers, trait objects and raw
/// pointers, whose HOL types are placeholder types without the store's type variables)?
pub fn has_mut_ref(t: Ty<'_>) -> bool {
    let mut w = t.walk();
    while let Some(g) = w.next() {
        match g.as_type().map(|x| *x.kind()) {
            Some(ty::Ref(_, _, m)) if m.is_mut() => return true,
            Some(ty::FnPtr(..) | ty::Dynamic(..) | ty::RawPtr(..)) => w.skip_current_subtree(),
            _ => {}
        }
    }
    false
}

/// Does one of the types `ts` (an ADT's field types) mention the ADT `did`?
pub fn mentions_adt(ts: &[Ty<'_>], did: DefId) -> bool {
    ts.iter().any(|t| t.walk().any(|g| matches!(g.as_type().map(|x| *x.kind()), Some(ty::Adt(a, _)) if a.did() == did)))
}

/// The constants the `simple_word_enum` declaration of the type `n` defines besides its
/// constructors (AutoCorrode's `Simple_Word_Enums` and `Case_for_Typedefs`).
pub fn word_enum_consts(n: &str) -> Vec<String> {
    vec![format!("{}_variants", n), format!("{}_all", n), format!("{}_index", n), format!("match_{}", n), format!("case_{}", n)]
}

pub fn field_ty<'tcx>(tcx: TyCtxt<'tcx>, f: &ty::FieldDef, args: GenericArgsRef<'tcx>, env: ty::TypingEnv<'tcx>) -> Ty<'tcx> {
    tcx.erase_and_anonymize_regions(try_normalize(tcx, env, f.ty(tcx, args)).expect("a field type normalises"))
}

/// `x` normalised in `env`, with erased regions. The aliases in types from type checking (and in
/// their instantiations) are marked rigid in its environment and mode, and normalisation skips rigid
/// aliases; the frontend normalises in other environments (post-analysis, the caller's for a callee's
/// types), so they are first made non-rigid, as rustc does for MIR after type checking
/// (`rustc_mir_transform::post_analysis_normalize`). Otherwise an `impl Trait` type is not revealed,
/// and a projection on one is not normalised.
pub fn try_normalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    env: ty::TypingEnv<'tcx>,
    x: ty::Unnormalized<'tcx, T>,
) -> Result<T, ty::normalize_erasing_regions::NormalizationError<'tcx>> {
    tcx.try_normalize_erasing_regions(env, ty::set_aliases_to_non_rigid(tcx, x.skip_normalization()))
}

/// `x` normalised in `env` (see `try_normalize`), or `x` itself (with erased regions) where it does
/// not normalise, as rustc keeps such types in MIR: a projection whose bound `env` implies only
/// through an equality the trait solver does not use (resolvo: `<<I as Interner>::SolvableId as
/// SolverId>::Set` under `I: Interner<SolvableId = S>`, without `S: SolverId`) stays a projection.
pub fn normalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>> + Copy>(tcx: TyCtxt<'tcx>, env: ty::TypingEnv<'tcx>, x: ty::Unnormalized<'tcx, T>) -> T {
    try_normalize(tcx, env, x).unwrap_or_else(|_| tcx.erase_and_anonymize_regions(x.skip_normalization()))
}

/// A HOL type written without redundant parentheses (every compound argument and operand
/// parenthesised, nothing else), to compare types written differently; the string itself if it
/// does not parse.
pub fn canonical_hol_ty(s: &str) -> String {
    // tokens: parentheses, commas, symbols (`\<times>`, `\<Rightarrow>`) and words
    let mut toks: Vec<String> = vec![];
    let mut cur = String::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' | ')' | ',' => {
                if !cur.is_empty() { toks.push(std::mem::take(&mut cur)) }
                toks.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() { toks.push(std::mem::take(&mut cur)) }
            }
            '\\' => {
                if !cur.is_empty() { toks.push(std::mem::take(&mut cur)) }
                let mut sym = String::from("\\");
                for d in chars.by_ref() {
                    sym.push(d);
                    if d == '>' { break }
                }
                toks.push(sym);
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() { toks.push(cur) }
    enum T {
        App(Vec<T>, String),
        Name(String),
        Bin(Box<T>, &'static str, Box<T>),
    }
    const TIMES: &str = "\\<times>";
    const FUN: &str = "\\<Rightarrow>";
    fn ty(t: &[String], i: &mut usize) -> Option<T> {
        let l = prod(t, i)?;
        if t.get(*i).map(|x| x.as_str()) == Some(FUN) {
            *i += 1;
            return Some(T::Bin(Box::new(l), "=>", Box::new(ty(t, i)?)));
        }
        Some(l)
    }
    fn prod(t: &[String], i: &mut usize) -> Option<T> {
        let l = app(t, i)?;
        if t.get(*i).map(|x| x.as_str()) == Some(TIMES) {
            *i += 1;
            return Some(T::Bin(Box::new(l), "*", Box::new(prod(t, i)?)));
        }
        Some(l)
    }
    fn app(t: &[String], i: &mut usize) -> Option<T> {
        let w = t.get(*i)?.clone();
        let mut args = if w == "(" {
            *i += 1;
            let mut v = vec![ty(t, i)?];
            while t.get(*i)? == "," {
                *i += 1;
                v.push(ty(t, i)?);
            }
            if t.get(*i)? != ")" { return None }
            *i += 1;
            v
        } else if w == ")" || w == "," || w == TIMES || w == FUN {
            return None;
        } else {
            *i += 1;
            vec![T::Name(w)]
        };
        // postfix type constructors
        while let Some(c) = t.get(*i)
            && !(c == "(" || c == ")" || c == "," || c == TIMES || c == FUN)
        {
            *i += 1;
            args = vec![T::App(args, c.clone())];
        }
        if args.len() == 1 { args.pop() } else { None }
    }
    fn show(x: &T) -> String {
        match x {
            T::Name(n) => n.clone(),
            T::App(a, c) => format!("({}) {}", a.iter().map(show).collect::<Vec<_>>().join(", "), c),
            T::Bin(l, o, r) => format!("({} {} {})", show(l), o, show(r)),
        }
    }
    let mut i = 0;
    match ty(&toks, &mut i) {
        Some(x) if i == toks.len() => show(&x),
        _ => s.to_string(),
    }
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
            alloc_keys: vec![],
            fn_items: Vec::new(),
            fmt_error: fmt_error_of(tcx),
            std_adts: std_adts_of(tcx),
            fmt_traits: fmt_traits_of(tcx),
            opaques: Vec::new(),
            placeholders: Vec::new(),
            placeholder_type_uses: 0,
            fun_defs: Vec::new(),
            item_comments: Vec::new(),
            marker_ids: Vec::new(),
            marker_index: HashMap::new(),
            mono_fns: HashSet::new(),
            has_drop_impls: false,
            instance_names: HashMap::new(),
            copy_names: HashMap::new(),
            dict_traits: Vec::new(),
            dict_names: HashMap::new(),
            instances_per_fn: HashMap::new(),
            pending: Vec::new(),
            opaque_adts: HashMap::new(),
            record_adts: HashSet::new(),
            ref_adts: HashSet::new(),
            alias_tvars: None,
            adt_projs: HashMap::new(),
            proj_tvars: None,
            proj_env: None,
            dict_methods_memo: Default::default(),
            own_dict_bounds_memo: Default::default(),
            fn_params: HashMap::new(),
            alloc_sites: Vec::new(),
            gen_calls: Vec::new(),
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

    /// The function to call for the local item `did` at the generic arguments `args`: an instance
    /// (queued for translation) if `did` is translated per instance and `args` are concrete,
    /// otherwise the item itself. `None` if `did` already has `MAX_INSTANCES` instances.
    pub fn callee(&mut self, did: DefId, args: GenericArgsRef<'tcx>) -> Option<FnKey<'tcx>> {
        // an instance at a type without a uRust model (e.g. a closure type) could not be
        // translated; the generic function, whose type variable it instantiates, is called instead
        if !self.mono_fns.contains(&did) || args.has_param() || !args.types().all(|t| self.ty_dry(t).1) {
            return Some((did, Inst::Generic));
        }
        self.instance(did, args)
    }

    /// The instance of the local item `did` at the concrete generic arguments `args` (queued for
    /// translation the first time). `None` if `did` already has `MAX_INSTANCES` instances.
    pub fn instance(&mut self, did: DefId, args: GenericArgsRef<'tcx>) -> Option<FnKey<'tcx>> {
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
            self.pending.push((did, Inst::Mono(args)));
        }
        Some((did, Inst::Mono(args)))
    }

    /// The copy of the trait default method `did` for the implementation `imp` (queued for
    /// translation the first time), named after the implementation's items.
    pub fn impl_copy(&mut self, did: DefId, imp: DefId) -> FnKey<'tcx> {
        if !self.copy_names.contains_key(&(did, imp)) {
            let mut segs = self.path_segments(imp);
            segs.push(self.tcx.item_name(did).to_string());
            let n = unique(names::global_name(&segs), |n| self.used_names.contains(n));
            self.used_names.insert(n.clone());
            self.copy_names.insert((did, imp), n);
            self.pending.push((did, Inst::ImplCopy(imp)));
        }
        (did, Inst::ImplCopy(imp))
    }

    /// HOL name of a function (`def_name` of the item, or the name of the instance or copy).
    pub fn fn_name(&mut self, key: FnKey<'tcx>) -> String {
        match key.1 {
            Inst::Generic => self.def_name(key.0),
            Inst::Mono(args) => self.instance_names[&(key.0, args)].clone(),
            Inst::ImplCopy(imp) => self.copy_names[&(key.0, imp)].clone(),
        }
    }

    /// The generic arguments `key` instantiates its item's generic parameters with, if any: an
    /// instance's, or for a default method's copy the implementation's trait arguments (and its
    /// own lifetimes, erased).
    pub fn inst_args(&self, key: FnKey<'tcx>) -> Option<GenericArgsRef<'tcx>> {
        match key.1 {
            Inst::Generic => None,
            Inst::Mono(args) => Some(args),
            Inst::ImplCopy(imp) => {
                let tr = self.tcx.impl_trait_ref(imp).instantiate_identity().skip_normalization();
                let parent = tr.args.len();
                Some(ty::GenericArgs::for_item(self.tcx, key.0, |p, _| {
                    if (p.index as usize) < parent { tr.args[p.index as usize] } else { self.tcx.lifetimes.re_erased.into() }
                }))
            }
        }
    }

    /// The typing environment of the body of `key`: an instance has no generic parameters left,
    /// a copy has those of its implementation, with the implementation's bounds and the method's
    /// own (at the implementation's trait reference).
    pub fn inst_env(&self, key: FnKey<'tcx>) -> ty::TypingEnv<'tcx> {
        let tcx = self.tcx;
        match key.1 {
            Inst::Generic => ty::TypingEnv::post_analysis(tcx, key.0),
            Inst::Mono(_) => ty::TypingEnv::fully_monomorphized(),
            Inst::ImplCopy(imp) => {
                let at = self.inst_args(key).expect("a copy has the arguments of its implementation");
                // (normalised there, as rustc normalises a typing environment: `<Foo<T> as Tr>::A:
                // Clone` is `T: Clone` under `type A = T`)
                let ienv = ty::TypingEnv::post_analysis(tcx, imp);
                let own = tcx.clauses_of(key.0).instantiate_own(tcx, at).map(|(c, _)| normalize(tcx, ienv, c));
                let clauses: Vec<ty::Clause<'tcx>> = tcx.param_env(imp).caller_bounds().chain(own).collect();
                let pe = ty::ParamEnv::new(tcx, ty::elaborate::elaborate(tcx, clauses));
                ty::TypingEnv::new(pe, ty::TypingMode::non_body_analysis()).with_post_analysis_normalized(tcx)
            }
        }
    }

    /// `x` (from the type-checking results of the body of `key.0`) as the body of `key` sees it:
    /// at its generic arguments, normalised in its typing environment.
    pub fn at_key<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(&self, key: FnKey<'tcx>, x: T) -> T {
        let env = self.inst_env(key);
        let x = match self.inst_args(key) {
            Some(args) => ty::EarlyBinder::bind(self.tcx, x).instantiate(self.tcx, args),
            None => ty::Unnormalized::new_wip(x),
        };
        normalize(self.tcx, env, x)
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

    /// `base` made unique among the HOL names of constants and types, and reserved.
    pub fn unique_global(&mut self, base: String) -> String {
        let n = unique(base, |n| self.used_names.contains(n) || self.used_type_names.contains(n));
        self.used_names.insert(n.clone());
        self.used_type_names.insert(n.clone());
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
        if self.word_enum(did, &n).is_some() {
            self.used_names.extend(word_enum_consts(&n));
        }
        self.type_names.insert(did, n.clone());
        n
    }

    /// For an enum whose variants (at least one) all have no fields: the bit width of its
    /// discriminant type and each variant's discriminant, as a word of that width. Such an enum
    /// is a `simple_word_enum` (AutoCorrode), whose declaration scales with the number of
    /// variants, unlike a `datatype` (distinctness of all pairs of constructors).
    /// `n` is its HOL name: an enum whose constructor names (`n_V`) would be among the constants
    /// `simple_word_enum` defines (see `word_enum_consts`) is not one.
    pub fn word_enum(&self, adt: DefId, n: &str) -> Option<(u64, Vec<u128>)> {
        let tcx = self.tcx;
        let def = tcx.adt_def(adt);
        if !def.is_enum() || def.variants().is_empty() || def.variants().iter().any(|v| !v.fields.is_empty()) {
            return None;
        }
        let consts = word_enum_consts(n);
        if def.variants().iter().any(|v| consts.contains(&format!("{}_{}", n, names::ident_chars(v.name.as_str())))) {
            return None;
        }
        let width = match def.repr().discr_type() {
            rustc_abi::IntegerType::Pointer(_) => tcx.data_layout.pointer_size().bits(),
            rustc_abi::IntegerType::Fixed(i, _) => i.size().bits(),
        };
        // `Discr::val` is the discriminant's bits in its type (e.g. `-1i8` is 0xff)
        Some((width, def.discriminants(tcx).map(|(_, d)| d.val).collect()))
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
        } else if lang(LangItem::RangeFrom) {
            "RangeFrom"
        } else if lang(LangItem::RangeTo) {
            "RangeTo"
        } else if lang(LangItem::RangeToInclusive) {
            "RangeToInclusive"
        } else if lang(LangItem::RangeFull) {
            "RangeFull"
        } else if diag(Symbol::intern("Formatter")) {
            "Formatter"
        } else if Some(did) == self.fmt_error {
            "FmtError"
        } else if diag(Symbol::intern("SliceIter")) {
            "SliceIter"
        } else if diag(Symbol::intern("Enumerate")) {
            "Enumerate"
        } else if diag(sym::HashMap) {
            "HashMap"
        } else if diag(Symbol::intern("HashMapEntry")) {
            "HashMapEntry"
        } else if let Some(&(_, n)) = self.std_adts.iter().find(|(d, _)| *d == did) {
            n
        } else {
            return None;
        })
    }

    /// The step function (AutoCorrode's `iter_step`, see `STD_MODELS.md`) of the iterator type `t`
    /// for its `next` (or, if `back`, its `next_back`), when it has a model.
    pub fn iter_step(&self, t: Ty<'tcx>, back: bool) -> Option<String> {
        let ty::Adt(def, args) = t.kind() else { return None };
        let inner = |i: usize| args.types().nth(i).expect("type argument of an iterator adapter");
        Some(match (self.std_adt(def.did())?, back) {
            ("SliceIter" | "SliceIterMut" | "VecIntoIter" | "Lines" | "SplitWhitespace" | "Chars", false) => "list_iter_next".into(),
            ("SliceIter" | "SliceIterMut" | "VecIntoIter" | "Lines" | "SplitWhitespace" | "Chars", true) => "list_iter_next_back".into(),
            ("ChunksExact", false) => "chunks_exact_next".into(),
            ("Chunks", false) => "chunks_next".into(),
            // `Filter::next` is the inner `find`, which takes the crate's fuel
            ("Filter", false) => format!("(filter_next urust_fuel {})", self.iter_step(inner(0), false)?),
            // `a..` over an unsigned integer (its state is the next value, see `ty`)
            ("RangeFrom", false) if matches!(inner(0).kind(), ty::Uint(_)) => "range_from_next".into(),
            // `a..b`, `a..=b` over an unsigned integer (a `range` record), from either end
            ("Range" | "RangeInclusive", false) if matches!(inner(0).kind(), ty::Uint(_)) => "range_next".into(),
            ("Range" | "RangeInclusive", true) if matches!(inner(0).kind(), ty::Uint(_)) => "range_next_back".into(),
            ("Enumerate", false) => format!("(enumerate_next {})", self.iter_step(inner(0), false)?),
            ("Zip", false) => format!("(zip_next {} {})", self.iter_step(inner(0), false)?, self.iter_step(inner(1), false)?),
            ("Skip", false) => format!("(skip_next {})", self.iter_step(inner(0), false)?),
            ("Take", false) => format!("(take_next {})", self.iter_step(inner(0), false)?),
            ("TakeWhile", false) => format!("(take_while_next {})", self.iter_step(inner(0), false)?),
            // `Map::next_back` is the inner `next_back`, mapped
            ("Map", b) => format!("(map_next {})", self.iter_step(inner(0), b)?),
            ("Rev", b) => self.iter_step(inner(0), !b)?,
            ("Copied" | "Cloned", b) => self.iter_step(inner(0), b)?,
            _ => return None,
        })
    }

    /// `core::fmt::Error`: the error type of the result of `Display::fmt`.

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
                // a field that does not normalise (only under impossible bounds, see `normalize`)
                // stays a projection, which has none
                def.all_fields().any(|f| {
                    let t = f.ty(tcx, args);
                    let t = normalize(tcx, env, t);
                    self.has_cell(tcx.erase_and_anonymize_regions(t), env, seen)
                })
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
            self.ext_types.insert(name.clone(), ExtType { arity, comment, ctors: vec![], params: vec![], deps: vec![], word: None, plain_enum: false });
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

    /// The key of the alias type `t` in `proj_tvars`: with erased regions, and its projections
    /// (also those in its arguments) not marked rigid, as normalisation marks some and not others
    /// (e.g. the inner projection of a slot `<<I as A>::X as B>::Y` and of the same type written in
    /// a signature).
    pub fn proj_key(&self, t: Ty<'tcx>) -> Option<ty::AliasTy<'tcx>> {
        let t = ty::set_aliases_to_non_rigid(self.tcx, self.tcx.erase_and_anonymize_regions(t)).skip_normalization();
        match t.kind() {
            ty::Alias(_, a) => Some(*a),
            _ => None,
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
                            add(normalize(self.tcx, env, at), &mut out);
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
                ty::IntTy::I128 => "128 sword".into(),
            },
            ty::Uint(ut) => match ut {
                ty::UintTy::U8 => "8 word".into(),
                ty::UintTy::U16 => "16 word".into(),
                ty::UintTy::U32 => "32 word".into(),
                ty::UintTy::U64 | ty::UintTy::Usize => "64 word".into(),
                ty::UintTy::U128 => "128 word".into(),
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
            ty::Param(p) => match self.fn_params.get(&p.index) {
                Some(f) => f.clone(),
                None => names::tvar_name(p.name.as_str()),
            },
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
                    // `a..`, `..b`, `..=b` by their only field; `..` has none
                    Some("RangeFrom") | Some("RangeTo") | Some("RangeToInclusive") => self.ty(targs[0]),
                    Some("RangeFull") => "unit".into(),
                    // iterators by their states (see `iter_step` and `STD_MODELS.md`): the remaining
                    // elements of a sequence, or an adapter's fields with the inner iterator's state
                    Some("SliceIter") | Some("VecIntoIter") => format!("{} list", paren_ty(&self.ty(targs[0]))),
                    // the references to the remaining elements
                    Some("SliceIterMut") => format!("(('addr, 'gv, {}) Global_Store.ref list)", self.ty(targs[0])),
                    Some("Chunks") => format!("({} list \\<times> 64 word \\<times> tnil)", paren_ty(&self.ty(targs[0]))),
                    Some("Filter") => {
                        format!("({} \\<times> {} \\<times> tnil)", paren_ty(&self.ty(targs[0])), paren_ty(&self.ty(targs[1])))
                    }
                    // a hash map whose iteration order is not observed: its entries (see `STD_MODELS.md`)
                    Some("HashMap") => {
                        format!("(({} \\<times> {} \\<times> tnil) list)", paren_ty(&self.ty(targs[0])), paren_ty(&self.ty(targs[1])))
                    }
                    // an entry: the map (a reference to it) and the key
                    Some("HashMapEntry") => format!(
                        "(('addr, 'gv, ({} \\<times> {} \\<times> tnil) list) Global_Store.ref \\<times> {} \\<times> tnil)",
                        paren_ty(&self.ty(targs[0])),
                        paren_ty(&self.ty(targs[1])),
                        paren_ty(&self.ty(targs[0]))
                    ),
                    Some("Lines") | Some("SplitWhitespace") => "String.literal list".into(),
                    Some("Chars") => "char list".into(),
                    Some("ChunksExact") => {
                        let t = paren_ty(&self.ty(targs[0]));
                        format!("({} list list \\<times> {} list \\<times> tnil)", t, t)
                    }
                    Some("Enumerate") | Some("Skip") | Some("Take") => {
                        format!("({} \\<times> 64 word \\<times> tnil)", paren_ty(&self.ty(targs[0])))
                    }
                    Some("Zip") | Some("Map") => {
                        format!("({} \\<times> {} \\<times> tnil)", paren_ty(&self.ty(targs[0])), paren_ty(&self.ty(targs[1])))
                    }
                    Some("TakeWhile") => {
                        format!("({} \\<times> bool \\<times> {} \\<times> tnil)", paren_ty(&self.ty(targs[0])), paren_ty(&self.ty(targs[1])))
                    }
                    Some("Rev") | Some("Copied") | Some("Cloned") => self.ty(targs[0]),
                    Some("ParseIntError") => "int_error_kind".into(),
                    Some("TryFromSliceError") => "try_from_slice_error".into(),
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
                                let at = ty::EarlyBinder::bind(self.tcx, p).instantiate(self.tcx, *args);
                                let at = match self.proj_env {
                                    Some(env) => normalize(self.tcx, env, at),
                                    None => at.skip_normalization(),
                                };
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
                if let Some(m) = self.proj_tvars.as_ref() && let Some(v) = self.proj_key(t).and_then(|a| m.get(&a)) {
                    return v.clone();
                }
                if !t.has_escaping_bound_vars() && !t.has_param() && let Ok(n) = try_normalize(self.tcx, ty::TypingEnv::fully_monomorphized(), rustc_middle::ty::Unnormalized::new_wip(t)) {
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

    /// The locale's allocator for the HOL type `hol_ty` (its index in `alloc_types`), added if new.
    pub fn need_alloc(&mut self, hol_ty: &str) -> usize {
        // the same type may be written with different parentheses: one storage per type (else the
        // overloading of `store_reference_const` is ambiguous)
        let key = canonical_hol_ty(hol_ty);
        match self.alloc_keys.iter().position(|t| *t == key) {
            Some(k) => k,
            None => {
                self.alloc_keys.push(key);
                self.alloc_types.push(hol_ty.to_string());
                self.alloc_types.len() - 1
            }
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
        let comment = format!("Rust: {}", self.tcx.def_path_str(did));
        self.ext_types.insert(n.clone(), ExtType { arity, comment, ctors: vec![], params: vec![], deps: vec![], word: None, plain_enum: false });
        self.ext_type_ids.insert(did, n.clone());
        // the fields' type parameters are the ADT's (see `ext_fun`; `ext_datatype` sets its own
        // projections' type variables and typing environment)
        let fn_params = std::mem::take(&mut self.fn_params);
        let datatype = self.ext_datatype(did, &n);
        self.fn_params = fn_params;
        if let Some((params, ctors, deps, self_field)) = datatype {
            let word = self.word_enum(did, &n);
            if word.is_some() {
                self.used_names.extend(word_enum_consts(&n));
            }
            let plain_enum = self.tcx.adt_def(did).is_enum() && params.is_empty() && !self_field;
            let t = self.ext_types.get_mut(&n).expect("registered above");
            (t.params, t.ctors, t.deps, t.word, t.plain_enum) = (params, ctors, deps, word, plain_enum);
        }
        n
    }

    /// The datatype of the external ADT `did` (named `n`), if it is an enum or a struct with only
    /// public fields, without const parameters, whose field types all have uRust models and contain
    /// no `&mut` reference (see `ExtType`). Its associated types become `adt_projs`, as for local
    /// ADTs.
    /// Also tells whether a field mentions the ADT itself (see `mentions_adt`).
    fn ext_datatype(&mut self, did: DefId, n: &str) -> Option<(Vec<String>, Vec<(String, Vec<String>)>, Vec<String>, bool)> {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(did), DefKind::Enum | DefKind::Struct) { return None }
        let def = tcx.adt_def(did);
        if def.variants().is_empty() || (def.is_struct() && !def.non_enum_variant().fields.iter().all(|f| f.vis.is_public())) {
            return None;
        }
        if tcx.generics_of(did).own_params.iter().any(|p| matches!(p.kind, ty::GenericParamDefKind::Const { .. })) {
            return None;
        }
        let (own, env) = (ty::GenericArgs::identity_for_item(tcx, did), ty::TypingEnv::post_analysis(tcx, did));
        let ftys: Vec<Vec<Ty<'tcx>>> =
            def.variants().iter().map(|v| v.fields.iter().map(|f| field_ty(tcx, f, own, env)).collect()).collect();
        let all: Vec<Ty<'tcx>> = ftys.iter().flatten().copied().collect();
        // a `&mut` reference in a field is a HOL type over the store's type variables `'addr`,
        // `'gv`, which a datatype in the external types template does not have as parameters
        if all.iter().any(|&t| has_mut_ref(t)) {
            return None;
        }
        let projs = self.projections(did, &all);
        let proj_names: Vec<String> = (0..projs.len()).map(|k| format!("'proj{}", k)).collect();
        let saved = (self.proj_tvars.take(), self.proj_env.replace(env));
        self.proj_tvars = Some(
            projs
                .iter()
                .zip(proj_names.iter())
                .map(|(p, v)| (self.proj_key(*p).expect("projections are aliases"), v.clone()))
                .collect(),
        );
        // modelled, checked without recording anything first
        let modelled = all.iter().all(|t| self.ty_dry(*t).1);
        let result = modelled.then(|| {
            let ctors: Vec<(String, Vec<String>)> = def
                .variants()
                .iter()
                .zip(&ftys)
                .map(|(v, ts)| {
                    let c = if def.is_struct() { format!("make_{}", n) } else { format!("{}_{}", n, names::ident_chars(v.name.as_str())) };
                    (c, ts.iter().map(|t| self.ty(*t)).collect())
                })
                .collect();
            let mut deps = vec![];
            for t in &all {
                for g in t.walk() {
                    if let Some(ty::Adt(d, _)) = g.as_type().map(|x| x.kind())
                        && let Some(m) = self.ext_type_ids.get(&d.did())
                        && m != n
                        && !deps.contains(m)
                    {
                        deps.push(m.clone());
                    }
                }
            }
            let mut params: Vec<String> = own.types().map(|t| self.ty(t)).collect();
            params.extend(proj_names.iter().cloned());
            (params, ctors, deps, mentions_adt(&all, did))
        });
        (self.proj_tvars, self.proj_env) = saved;
        if result.is_some() && !projs.is_empty() {
            self.adt_projs.insert(did, projs);
        }
        result
    }

    /// Register the external ADTs occurring in `tys`: whether such a datatype takes associated
    /// types as parameters (`adt_projs`) must be known before the projections of types using it
    /// are computed (see `projections`).
    pub fn register_ext_adts(&mut self, tys: &[Ty<'tcx>]) {
        for &t in tys {
            let mut w = t.walk();
            while let Some(g) = w.next() {
                let Some(x) = g.as_type() else { continue };
                match x.kind() {
                    // parts without a HOL counterpart (see `ty`)
                    ty::Alias(..) | ty::RawPtr(..) | ty::FnPtr(..) | ty::Dynamic(..) => w.skip_current_subtree(),
                    ty::Adt(d, a) => match self.hol_kept_args(d.did()) {
                        Some(k) => {
                            w.skip_current_subtree();
                            let kept: Vec<Ty<'tcx>> = a.types().take(k).collect();
                            self.register_ext_adts(&kept);
                        }
                        None if !d.did().is_local() && self.std_adt(d.did()).is_none() => {
                            self.ext_type(d.did(), a.types().count());
                        }
                        None => {}
                    },
                    _ => {}
                }
            }
        }
    }

    /// For a standard ADT modelled by a HOL type that keeps only its first type arguments (see
    /// `ty`), how many it keeps (e.g. `Vec<T, A>` is `T list`).
    pub fn hol_kept_args(&self, did: DefId) -> Option<usize> {
        match self.std_adt(did)? {
            "Box" | "Vec" | "Option" | "Range" | "RangeInclusive" | "RangeFrom" | "RangeTo" | "RangeToInclusive" => Some(1),
            "String" | "Ordering" | "Formatter" | "FmtError" | "RangeFull" => Some(0),
            // the iterators keep all their type arguments (see `ty`)
            "SliceIter" | "SliceIterMut" | "ChunksExact" | "Chunks" | "VecIntoIter" | "Enumerate" | "Skip" | "Take" | "Rev" | "Copied" | "Cloned" => Some(1),
            "Zip" | "TakeWhile" | "Map" | "Filter" | "HashMap" | "HashMapEntry" => Some(2),
            "Lines" | "SplitWhitespace" | "Chars" | "ParseIntError" | "TryFromSliceError" => Some(0),
            _ => None,
        }
    }

    /// The constructor of the variant `vidx` of the external ADT `adt` when it is declared with
    /// its constructors (see `ExtType::ctors`), and whether the variant has fields.
    pub fn ext_ctor(&mut self, adt: DefId, vidx: usize) -> Option<(String, bool)> {
        if !matches!(self.tcx.def_kind(adt), DefKind::Enum | DefKind::Struct) { return None }
        let arity = self.tcx.generics_of(adt).own_counts().types;
        let n = self.ext_type(adt, arity);
        self.ext_types.get(&n).and_then(|t| t.ctors.get(vidx)).map(|(c, fs)| (c.clone(), !fs.is_empty()))
    }

    // ------------------------------------------------------------------
    // External functions
    // ------------------------------------------------------------------

    /// Whether the item `did` has const generic parameters of its own: it is translated only per
    /// instance (see `translate::run`), where they are constants.
    pub fn has_const_params(&self, did: DefId) -> bool {
        self.tcx.generics_of(did).own_params.iter().any(|p| matches!(p.kind, ty::GenericParamDefKind::Const { .. }))
    }

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
        // the signature's type parameters are the external function's, not those of the item being
        // translated: its `Fn`-bounded parameters (by index), its projections' type variables and its
        // typing environment do not apply (the signature's projections are `alias_tvars`)
        let saved = (std::mem::take(&mut self.fn_params), self.proj_tvars.take(), self.proj_env.take());
        self.alias_tvars = Some(0);
        let params: Vec<String> = sig.inputs().iter().map(|t| self.ty(*t)).collect();
        let ret = self.ty(sig.output());
        self.alias_tvars = None;
        (self.fn_params, self.proj_tvars, self.proj_env) = saved;
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

/// `core::fmt::Error`: the error type of the result of `Display::fmt`.
fn fmt_error_of(tcx: TyCtxt<'_>) -> Option<DefId> {
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

/// The standard library ADTs with models that have no lang or diagnostic item of their own,
/// identified by the compiler as the result types of methods it identifies: the iterator adapters
/// returned by methods of `Iterator`, the iterators returned by methods of the inherent impls of
/// `str` and of slices (found through their methods with diagnostic items), and `ParseIntError`,
/// the error type of `FromStr` for the integer types.
fn std_adts_of(tcx: TyCtxt<'_>) -> Vec<(DefId, &'static str)> {
    let mut out: Vec<(DefId, &'static str)> = vec![];
    let result_adt = |f: DefId| match tcx.fn_sig(f).skip_binder().output().skip_binder().kind() {
        ty::Adt(d, _) => Some(d.did()),
        _ => None,
    };
    let mut methods_of = |owner: DefId, methods: &[(&str, &'static str)]| {
        for &(m, n) in methods {
            let item = tcx.associated_items(owner).filter_by_name_unhygienic(Symbol::intern(m)).find(|i| i.is_fn());
            if let Some(d) = item.and_then(|i| result_adt(i.def_id)) {
                out.push((d, n));
            }
        }
    };
    if let Some(it) = tcx.get_diagnostic_item(sym::Iterator) {
        let adapters = [
            ("zip", "Zip"),
            ("skip", "Skip"),
            ("take", "Take"),
            ("take_while", "TakeWhile"),
            ("map", "Map"),
            ("filter", "Filter"),
            ("rev", "Rev"),
            ("copied", "Copied"),
            ("cloned", "Cloned"),
        ];
        methods_of(it, &adapters);
    }
    if let Some(sw) = tcx.get_diagnostic_item(Symbol::intern("str_split_whitespace")) {
        methods_of(tcx.parent(sw), &[("split_whitespace", "SplitWhitespace"), ("lines", "Lines"), ("chars", "Chars")]);
    }
    if let Some(si) = tcx.get_diagnostic_item(Symbol::intern("slice_iter")) {
        methods_of(tcx.parent(si), &[("chunks_exact", "ChunksExact"), ("chunks", "Chunks"), ("iter_mut", "SliceIterMut")]);
    }
    // `<u8 as FromStr>::Err`: the associated type `Err` of the implementation of `FromStr` (the
    // trait of the method `from_str_method`) for `u8`
    if let Some(from_str) = tcx.get_diagnostic_item(Symbol::intern("from_str_method")).map(|m| tcx.parent(m)) {
        for &imp in tcx.all_impls(from_str).collect::<Vec<_>>().iter() {
            if *tcx.type_of(imp).instantiate_identity().skip_normalization().kind() != ty::Uint(ty::UintTy::U8) { continue }
            let err = tcx.associated_items(imp).filter_by_name_unhygienic(sym::Err).next();
            if let Some(err) = err
                && let ty::Adt(d, _) = tcx.type_of(err.def_id).instantiate_identity().skip_normalization().kind()
            {
                out.push((d.did(), "ParseIntError"));
            }
        }
    }
    // `vec::IntoIter`: the associated type `IntoIter` of the implementation of `IntoIterator` for
    // `Vec<T>` (by value)
    if let (Some(into_iter), Some(vec)) = (tcx.get_diagnostic_item(sym::IntoIterator), tcx.get_diagnostic_item(sym::Vec)) {
        for imp in tcx.all_impls(into_iter).collect::<Vec<_>>() {
            let self_ty = tcx.type_of(imp).instantiate_identity().skip_normalization();
            if !matches!(self_ty.kind(), ty::Adt(d, _) if d.did() == vec) { continue }
            let it = tcx.associated_items(imp).filter_by_name_unhygienic(Symbol::intern("IntoIter")).next();
            if let Some(it) = it
                && let ty::Adt(d, _) = tcx.type_of(it.def_id).instantiate_identity().skip_normalization().kind()
            {
                out.push((d.did(), "VecIntoIter"));
            }
        }
    }
    // `TryFromSliceError`: the associated type `Error` of the implementation of `TryFrom<&[T]>`
    // for arrays `[T; N]`
    if let Some(try_from) = tcx.get_diagnostic_item(sym::TryFrom) {
        for imp in tcx.all_impls(try_from).collect::<Vec<_>>() {
            let tr = tcx.impl_trait_ref(imp).instantiate_identity().skip_normalization();
            let from_slice = matches!(tr.args.type_at(1).kind(), ty::Ref(_, s, _) if s.is_slice());
            if !from_slice || !matches!(tr.args.type_at(0).kind(), ty::Array(..)) { continue }
            let err = tcx.associated_items(imp).filter_by_name_unhygienic(Symbol::intern("Error")).next();
            if let Some(err) = err
                && let ty::Adt(d, _) = tcx.type_of(err.def_id).instantiate_identity().skip_normalization().kind()
                && !out.iter().any(|(x, _)| *x == d.did())
            {
                out.push((d.did(), "TryFromSliceError"));
            }
        }
    }
    out
}

/// The traits bounding the type parameters of the constructors of `fmt::rt::Argument` (the lang
/// item `format_argument`), named by their item names: the formatting traits of `format_args!`.
fn fmt_traits_of(tcx: TyCtxt<'_>) -> Vec<(DefId, String)> {
    let Some(arg) = tcx.lang_items().get(LangItem::FormatArgument) else { return vec![] };
    let mut out: Vec<(DefId, String)> = vec![];
    for &imp in tcx.inherent_impls(arg) {
        for item in tcx.associated_items(imp).in_definition_order().filter(|i| i.is_fn()) {
            for c in tcx.param_env(item.def_id).caller_bounds() {
                if let Some(t) = c.as_trait_clause().map(|t| t.def_id())
                    && tcx.associated_items(t).in_definition_order().any(|i| i.is_fn())
                    && !out.iter().any(|(d, _)| *d == t)
                {
                    out.push((t, tcx.item_name(t).to_string()));
                }
            }
        }
    }
    out
}
