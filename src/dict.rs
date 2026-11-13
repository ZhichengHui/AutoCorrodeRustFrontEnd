//! Trait dictionaries (dictionary passing, as in Aeneas).
//!
//! A trait is a HOL datatype with one field per method (a uRust function value) and one per
//! supertrait (the supertrait's dictionary); an implementation is a value of it. A generic item
//! takes one dictionary parameter per trait bound of its signature, and a call in its body
//! resolved to a bound calls the field of the bound's dictionary. The associated types of a
//! trait, those of its supertraits, and those of its other type parameters that its fields' types
//! have, are type parameters of its datatype ("slots").

use std::collections::HashMap;
use std::fmt::Write as _;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TypeVisitableExt};

use crate::frontend::{FnKey, Frontend, Inst, paren_ty};
use crate::names;

/// The type parameters every dictionary datatype takes first: those of `function_body` and of
/// references, which the field types use.
const BASE_TVARS: [&str; 6] = ["'s", "'abort", "'i", "'o", "'addr", "'gv"];

/// The datatype of a trait's dictionaries.
pub struct DictDecl {
    pub name: String,
    /// (field name, HOL type) of the methods, then of the supertraits
    pub fields: Vec<(String, String)>,
    pub tparams: Vec<String>,
}

/// Fields per datatype: the datatype package fails to prove the injectivity of a constructor with
/// many fields of large types (e.g. the 16 of `Hasher`'s dictionaries).
const MAX_FIELDS: usize = 8;

/// The datatype `name` with the fields `fields` (name, HOL type) and type parameters `tparams`, with
/// its constructor `name` and its selectors the field names. With more than `MAX_FIELDS` fields,
/// the fields are grouped into datatypes of their own (`name_p<k>`, recursively), the datatype of
/// `name` holds the groups (constructor `name_mk`, selectors `name_part<k>`), and the constructor
/// and the selectors of the fields are abbreviations through the groups.
fn record_decl(name: &str, tparams: &[String], fields: &[(String, String)]) -> String {
    let head = format!("({}) {}", tparams.join(", "), name);
    let groups = record_groups(name, fields.len());
    if groups.is_empty() {
        let fs: Vec<String> = fields.iter().map(|(f, t)| format!("({}: \\<open>{}\\<close>)", f, t)).collect();
        return format!("datatype {} =\n  {} {}\n\n", head, name, fs.join("\n    "));
    }
    let mut out = String::new();
    let mut rest = fields;
    let mut parts = vec![];
    for g in &groups {
        let (here, later) = rest.split_at(g.fields.len());
        rest = later;
        // the group's own fields, renamed (the field names are the abbreviations below)
        let pf: Vec<(String, String)> = g.fields.iter().cloned().zip(here.iter().map(|(_, t)| t.clone())).collect();
        out.push_str(&record_decl(&g.name, tparams, &pf));
        parts.push(format!("({}: \\<open>({}) {}\\<close>)", g.selector, tparams.join(", "), g.name));
    }
    let mk = record_constructor(name);
    out.push_str(&format!("datatype {} =\n  {} {}\n\n", head, mk, parts.join("\n    ")));
    let xs: Vec<String> = (0..fields.len()).map(|i| format!("x{}", i)).collect();
    let mut i = 0;
    let mut args = vec![];
    for g in &groups {
        args.push(format!("({} {})", g.name, xs[i..i + g.fields.len()].join(" ")));
        i += g.fields.len();
    }
    out.push_str(&format!(
        "abbreviation (input) {} where\n  \\<open>{} \\<equiv> \\<lambda>{}. {} {}\\<close>\n\n",
        name,
        name,
        xs.join(" "),
        mk,
        args.join(" ")
    ));
    let mut gi = fields.iter();
    for g in &groups {
        for sel in &g.fields {
            let (f, _) = gi.next().expect("a field per group field");
            out.push_str(&format!(
                "abbreviation (input) {} where\n  \\<open>{} \\<equiv> \\<lambda>d. {} ({} d)\\<close>\n\n",
                f, f, sel, g.selector
            ));
        }
    }
    out
}

/// A group of the fields of a datatype with more than `MAX_FIELDS` fields (see `record_decl`).
struct RecordGroup {
    /// the selector of the group in the datatype (`name_part<k>`)
    selector: String,
    /// the group's datatype (`name_p<k>`)
    name: String,
    /// the group's datatype's fields (`name_p<k>_<j>`), one per field of the group, in order
    fields: Vec<String>,
}

/// The groups of the fields of the datatype `name` with `n` fields as `record_decl` declares them,
/// in order: none with at most `MAX_FIELDS` fields, else groups of at most `MAX_FIELDS` fields (at
/// least `MAX_FIELDS`, so that a group itself may be grouped again).
fn record_groups(name: &str, n: usize) -> Vec<RecordGroup> {
    if n <= MAX_FIELDS {
        return vec![];
    }
    let size = n.div_ceil(MAX_FIELDS).max(MAX_FIELDS);
    (0..n.div_ceil(size))
        .map(|k| {
            let pn = format!("{}_p{}", name, k);
            let m = size.min(n - k * size);
            RecordGroup { selector: format!("{}_part{}", name, k), fields: (0..m).map(|j| format!("{}_{}", pn, j)).collect(), name: pn }
        })
        .collect()
}

/// The constructor of the datatype `name` holding its groups (see `record_decl`).
fn record_constructor(name: &str) -> String {
    format!("{}_mk", name)
}

/// The names of the constants and types that `record_decl` declares for the datatype `name` with
/// `n` fields, other than `name` and the field names: those of its groups (see `record_groups`).
fn record_group_names(name: &str, n: usize) -> Vec<String> {
    let groups = record_groups(name, n);
    if groups.is_empty() {
        return vec![];
    }
    let mut out = vec![record_constructor(name)];
    for g in groups {
        out.push(g.selector);
        out.extend(record_group_names(&g.name, g.fields.len()));
        out.extend(g.fields);
        out.push(g.name);
    }
    out
}

impl<'tcx> Frontend<'tcx> {
    /// `Fn`, `FnMut`, `FnOnce`: a bound by one of them is the function value itself.
    pub fn is_fn_trait(&self, tr: DefId) -> bool {
        self.tcx.fn_trait_kind_from_def_id(tr).is_some()
    }

    /// The methods of `tr` that are fields of its dictionaries: those without type parameters of
    /// their own (a field cannot be polymorphic: HOL has no rank-2 types; see `monomorphic_methods`)
    /// whose field types have no associated types other than the slots of the dictionaries of `tr`
    /// (the type variables of a field's type): neither their signatures nor the dictionary types of
    /// their own bounds (see `own_dict_bounds`; e.g. not `where Self::Item: HasAssoc`, whose
    /// dictionaries have the slot `<Self::Item as HasAssoc>::Assoc`). Nor are those with an own bound
    /// by a trait whose dictionaries contain those of `tr` (see `reaches_through_methods`; e.g.
    /// `Iterator::rev`, `where Self: DoubleEndedIterator`, a subtrait of `Iterator`): the datatypes
    /// would be mutually recursive through a function argument, which HOL does not admit.
    pub fn dict_methods(&self, tr: DefId) -> Vec<DefId> {
        if let Some(ms) = self.dict_methods_memo.borrow().get(&tr) {
            return ms.clone();
        }
        let ms = self.find_dict_methods(tr);
        self.dict_methods_memo.borrow_mut().insert(tr, ms.clone());
        ms
    }

    fn find_dict_methods(&self, tr: DefId) -> Vec<DefId> {
        let tcx = self.tcx;
        let slots: Vec<ty::AliasTy<'tcx>> = self
            .dict_slots(ty::TraitRef::identity(tcx, tr))
            .into_iter()
            .map(|s| self.proj_key(s).expect("slots are projections"))
            .collect();
        self.field_candidates(tr)
            .into_iter()
            .filter(|&m| self.field_projections(m).iter().all(|&p| self.proj_key(p).is_some_and(|k| slots.contains(&k))))
            .collect()
    }

    /// The methods of `tr` that may be fields of its dictionaries (see `dict_methods`): those
    /// without type parameters of their own (see `monomorphic_methods`) none of whose own bounds
    /// is by a trait whose dictionaries contain those of `tr`.
    fn field_candidates(&self, tr: DefId) -> Vec<DefId> {
        self.monomorphic_methods(tr)
            .into_iter()
            .filter(|&m| !self.own_dict_bounds(m).iter().any(|b| self.reaches_through_methods(b.def_id, tr, &mut vec![])))
            .collect()
    }

    /// The argument and result types of the trait method `m` (in its trait's parameters).
    fn sig_types(&self, m: DefId) -> Vec<Ty<'tcx>> {
        let tcx = self.tcx;
        tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(m).instantiate_identity().skip_normalization()).inputs_and_output.to_vec()
    }

    /// The associated-type projections in the type of the dictionary field of the trait method `m`
    /// (see `dict_decl`): in its signature and in the dictionary types of its own bounds (their
    /// arguments and slots, see `own_dict_bounds`), those written and those that the datatypes of
    /// ADTs in them take as type parameters (see `projections`; normalised in `m`'s typing
    /// environment, as `dict_decl` translates them).
    fn field_projections(&self, m: DefId) -> Vec<Ty<'tcx>> {
        if let Some(ps) = self.field_projections_memo.borrow().get(&m) {
            return ps.clone();
        }
        let tcx = self.tcx;
        let env = ty::TypingEnv::post_analysis(tcx, m);
        let mut tys = self.sig_types(m);
        for b in self.own_dict_bounds(m) {
            tys.extend(b.args.types());
            tys.extend(self.dict_slots(b).into_iter().map(|s| crate::frontend::normalize(tcx, env, ty::Unnormalized::new_wip(s))));
        }
        let ps = self.assoc_projections(m, &tys);
        self.field_projections_memo.borrow_mut().insert(m, ps.clone());
        ps
    }

    /// The associated-type projections among `projections(did, tys)`.
    fn assoc_projections(&self, did: DefId, tys: &[Ty<'tcx>]) -> Vec<Ty<'tcx>> {
        self.projections(did, tys)
            .into_iter()
            .filter(|p| matches!(p.kind(), ty::Alias(_, a) if matches!(a.kind, ty::AliasTyKind::Projection { .. })))
            .collect()
    }

    /// The slots of the dictionaries of `tr` that are associated types of its type parameters other
    /// than `Self` named by its bounds (see `on_trait_param`; e.g. `<L as Language>::Discriminant`
    /// for `trait Analysis<L: Language>`). They are those in the field types of its methods that
    /// may be fields (see `field_candidates`, `field_projections`) without projections other than
    /// these and the trait's other slots (see `trait_slots`), in order of occurrence: exactly the
    /// projections other than those slots in the fields' types. A projection in a field's type may
    /// be written or be one that the datatype of an ADT in it takes as a type parameter
    /// (`&mut EGraph<L, Self>`, whose datatype takes `<L as Language>::Discriminant`). Then those
    /// such projections in the dictionary types of the supertraits and associated type bounds
    /// (see `dict_parents`; their arguments and slots, normalised in the trait's typing
    /// environment, as `dict_decl` translates them), which are fields in any case: a projection
    /// there that is not a slot is a placeholder type.
    fn param_slots(&self, tr: DefId) -> Vec<Ty<'tcx>> {
        if let Some(ps) = self.param_slots_memo.borrow().get(&tr) {
            return ps.clone();
        }
        let ps = self.find_param_slots(tr);
        self.param_slots_memo.borrow_mut().insert(tr, ps.clone());
        ps
    }

    fn find_param_slots(&self, tr: DefId) -> Vec<Ty<'tcx>> {
        let tcx = self.tcx;
        let base: Vec<ty::AliasTy<'tcx>> = self
            .trait_slots(ty::TraitRef::identity(tcx, tr))
            .into_iter()
            .map(|s| self.proj_key(s).expect("slots are projections"))
            .collect();
        let bounds = self.bound_keys(tr);
        let new = |ps: Vec<Ty<'tcx>>| -> Vec<Ty<'tcx>> { ps.into_iter().filter(|&p| !self.proj_key(p).is_some_and(|k| base.contains(&k))).collect() };
        let mut out: Vec<Ty<'tcx>> = vec![];
        let add = |ps: Vec<Ty<'tcx>>, out: &mut Vec<Ty<'tcx>>| {
            for p in ps {
                if !out.iter().any(|&q| self.proj_key(q) == self.proj_key(p)) {
                    out.push(p);
                }
            }
        };
        for m in self.field_candidates(tr) {
            let ps = new(self.field_projections(m));
            if ps.iter().all(|&p| self.on_trait_param(&bounds, p)) {
                add(ps, &mut out);
            }
        }
        let env = ty::TypingEnv::post_analysis(tcx, tr);
        for p in self.dict_parents(tr) {
            let mut tys: Vec<Ty<'tcx>> = p.args.types().collect();
            tys.extend(self.dict_slots(p).into_iter().map(|s| crate::frontend::normalize(tcx, env, ty::Unnormalized::new_wip(s))));
            let ps = new(self.assoc_projections(tr, &tys)).into_iter().filter(|&q| self.on_trait_param(&bounds, q)).collect();
            add(ps, &mut out);
        }
        out
    }

    /// The trait references of the bounds of the trait `tr` (its `where` clauses, elaborated),
    /// as `bound_key` compares them.
    fn bound_keys(&self, tr: DefId) -> Vec<ty::TraitRef<'tcx>> {
        let tcx = self.tcx;
        tcx.param_env(tr)
            .caller_bounds()
            .filter_map(|c| c.as_trait_clause())
            .filter(|c| c.polarity() == ty::ClausePolarity::Positive)
            .map(|c| self.bound_key(tcx.instantiate_bound_regions_with_erased(c).trait_ref))
            .collect()
    }

    /// The trait reference `r` with erased regions and its projections not marked rigid.
    fn bound_key(&self, r: ty::TraitRef<'tcx>) -> ty::TraitRef<'tcx> {
        ty::set_aliases_to_non_rigid(self.tcx, self.tcx.erase_and_anonymize_regions(r)).skip_normalization()
    }

    /// Is the projection `p` (in the parameters of a trait whose bounds are `bounds`, see
    /// `bound_keys`) an associated type of a type parameter of the trait other than `Self` (index
    /// 0), or of such a projection (e.g. `<L::A as B>::C` with the bound `L::A: B`), each named by
    /// one of `bounds` (not by a method's own bound, nor by the bounds of an associated type's
    /// declaration, which `bounds` does not have), so that wherever a trait reference of the trait
    /// holds, its projection is well-formed?
    fn on_trait_param(&self, bounds: &[ty::TraitRef<'tcx>], p: Ty<'tcx>) -> bool {
        let tcx = self.tcx;
        let mut t = p;
        loop {
            match t.kind() {
                ty::Alias(_, a) if matches!(a.kind, ty::AliasTyKind::Projection { .. }) => {
                    if !bounds.contains(&self.bound_key(a.trait_ref(tcx))) {
                        return false;
                    }
                    t = a.self_ty();
                }
                ty::Param(q) => return q.index != 0,
                _ => return false,
            }
        }
    }

    /// The methods of `tr` without type or const parameters of their own, other than those with
    /// `impl Trait` types and the standard library's internals.
    fn monomorphic_methods(&self, tr: DefId) -> Vec<DefId> {
        self.tcx
            .associated_items(tr)
            .in_definition_order()
            .filter(|i| i.is_fn())
            .filter(|i| {
                let c = self.tcx.generics_of(i.def_id).own_counts();
                // the unstable methods of the standard library's traits are its internals (e.g.
                // `PartialOrd::__chaining_lt`), which only it calls
                let internal = !i.def_id.is_local() && self.tcx.lookup_stability(i.def_id).is_some_and(|s| s.is_unstable());
                c.types == 0 && c.consts == 0 && !self.has_rpitit(i.def_id) && !internal
            })
            .map(|i| i.def_id)
            .collect()
    }

    /// Does the signature of the trait method `m` have an `impl Trait` type (the result type of a
    /// trait method may be one, a hidden associated type of the trait), which no field type
    /// expresses?
    fn has_rpitit(&self, m: DefId) -> bool {
        let tcx = self.tcx;
        let sig = tcx.fn_sig(m).instantiate_identity().skip_binder();
        sig.inputs_and_output.iter().any(|t| {
            t.walk().any(|g| match g.as_type().map(|x| *x.kind()) {
                Some(ty::Alias(_, a)) => match a.kind {
                    ty::AliasTyKind::Opaque { .. } => true,
                    ty::AliasTyKind::Projection { def_id } => tcx.opt_rpitit_info(def_id).is_some(),
                    _ => false,
                },
                _ => false,
            })
        })
    }

    /// The supertraits of `tr` (bounds on `Self`) and the bounds of its associated types (e.g.
    /// `<Self as IntoIterator>::IntoIter: Iterator`), as trait references on its own generic
    /// parameters, with whether each is a supertrait.
    fn trait_bounds(&self, tr: DefId) -> Vec<(ty::TraitRef<'tcx>, bool)> {
        let tcx = self.tcx;
        let mut clauses: Vec<(ty::Clause<'tcx>, bool)> =
            tcx.explicit_super_clauses_of(tr).skip_binder().iter().map(|(c, _)| (*c, true)).collect();
        for i in tcx.associated_items(tr).in_definition_order() {
            if matches!(i.kind, ty::AssocKind::Type { .. }) && self.is_slot(i.def_id) {
                clauses.extend(tcx.explicit_item_self_bounds(i.def_id).skip_binder().iter().map(|(c, _)| (*c, false)));
            }
        }
        let mut out: Vec<(ty::TraitRef<'tcx>, bool)> = vec![];
        for (c, sup) in clauses {
            let Some(p) = c.as_trait_clause() else { continue };
            let p = tcx.instantiate_bound_regions_with_erased(p);
            let r = tcx.erase_and_anonymize_regions(p.trait_ref);
            if p.polarity == ty::ClausePolarity::Positive && !out.iter().any(|(q, _)| *q == r) {
                out.push((r, sup));
            }
        }
        out
    }

    /// Does `from` reach the trait `to` through supertraits and associated type bounds?
    fn reaches(&self, from: DefId, to: DefId, seen: &mut Vec<DefId>) -> bool {
        if from == to {
            return true;
        }
        if seen.contains(&from) {
            return false;
        }
        seen.push(from);
        self.trait_bounds(from).into_iter().any(|(r, _)| self.reaches(r.def_id, to, seen))
    }

    /// Does `from` reach the trait `to` through supertraits, associated type bounds and the own bounds
    /// of its methods (see `own_dict_bounds`): may the dictionaries of `from` contain those of `to`
    /// (as fields, or as arguments of method fields)?
    fn reaches_through_methods(&self, from: DefId, to: DefId, seen: &mut Vec<DefId>) -> bool {
        if from == to {
            return true;
        }
        if seen.contains(&from) {
            return false;
        }
        seen.push(from);
        let own = self.monomorphic_methods(from).into_iter().flat_map(|m| self.own_dict_bounds(m));
        let next: Vec<DefId> = self.trait_bounds(from).into_iter().map(|(r, _)| r.def_id).chain(own.map(|r| r.def_id)).collect();
        next.into_iter().any(|t| self.reaches_through_methods(t, to, seen))
    }

    /// The bounds whose dictionaries are fields of the dictionaries of `tr` (see `trait_bounds`),
    /// those by traits with dictionaries. A bound of an associated type by a trait that reaches
    /// `tr` again (e.g. `trait Node { type Child: Node; }`) is not: the dictionary would contain
    /// itself.
    pub fn dict_parents(&self, tr: DefId) -> Vec<ty::TraitRef<'tcx>> {
        self.trait_bounds(tr)
            .into_iter()
            .filter(|(r, sup)| (*sup || !self.reaches(r.def_id, tr, &mut vec![])) && self.has_dict(r.def_id))
            .map(|(r, _)| r)
            .collect()
    }

    /// Does a bound by `tr` take a dictionary: does it have a method without type parameters of its
    /// own, a supertrait with a dictionary, or an associated type (a trait with associated types
    /// only has dictionaries without fields, whose slots are the type variables of its associated
    /// types, see `translate::slot_tvars`)? `Fn` bounds are function values instead.
    pub fn has_dict(&self, tr: DefId) -> bool {
        if self.is_fn_trait(tr) {
            return false;
        }
        // (not `dict_methods`, which needs the slots: a trait none of whose methods is a field has
        // dictionaries without method fields)
        !self.monomorphic_methods(tr).is_empty() || !self.dict_parents(tr).is_empty() || !self.own_slots(tr).is_empty()
    }

    /// The associated types of a trait reference that its dictionary datatype takes as type
    /// parameters: its trait's own (without generic parameters of their own), then those of its
    /// supertraits with dictionaries, in order, then those of its other type parameters (see
    /// `param_slots`).
    pub fn dict_slots(&self, r: ty::TraitRef<'tcx>) -> Vec<Ty<'tcx>> {
        let tcx = self.tcx;
        let mut out = self.trait_slots(r);
        for p in self.param_slots(r.def_id) {
            out.push(tcx.erase_and_anonymize_regions(ty::EarlyBinder::bind(tcx, p).instantiate(tcx, r.args).skip_normalization()));
        }
        out
    }

    /// The slots of `r` that are associated types of its trait and of its supertraits (with
    /// theirs, see `dict_slots`).
    fn trait_slots(&self, r: ty::TraitRef<'tcx>) -> Vec<Ty<'tcx>> {
        let tcx = self.tcx;
        let mut out: Vec<Ty<'tcx>> = self
            .own_slots(r.def_id)
            .into_iter()
            .map(|i| {
                let own = tcx.generics_of(i).own_params.len();
                let args = tcx.mk_args_from_iter(
                    r.args.iter().chain((0..own).map(|_| tcx.lifetimes.re_erased.into())),
                );
                // with erased regions, as the types the slots stand for in (erased) signatures
                tcx.erase_and_anonymize_regions(Ty::new_projection(tcx, ty::IsRigid::No, i, args))
            })
            .collect();
        for p in self.dict_parents(r.def_id) {
            let pr = ty::EarlyBinder::bind(tcx, p).instantiate(tcx, r.args).skip_normalization();
            out.extend(self.dict_slots(pr));
        }
        out
    }

    /// The associated types of `tr` that are slots of its dictionaries (see `is_slot`).
    pub fn own_slots(&self, tr: DefId) -> Vec<DefId> {
        self.tcx
            .associated_items(tr)
            .in_definition_order()
            .filter(|i| matches!(i.kind, ty::AssocKind::Type { .. }) && self.is_slot(i.def_id))
            .map(|i| i.def_id)
            .collect()
    }

    /// Is the associated type `at` a slot of its trait's dictionaries: has it no type or const
    /// parameters of its own (a slot cannot be a type constructor), and is it not the hidden type
    /// of a method returning `impl Trait`?
    pub fn is_slot(&self, at: DefId) -> bool {
        let tcx = self.tcx;
        tcx.generics_of(at).own_params.iter().all(|p| matches!(p.kind, ty::GenericParamDefKind::Lifetime))
            && tcx.opt_rpitit_info(at).is_none()
    }

    /// The HOL name of the dictionary datatype of `tr` (also the name of its constructor). The
    /// names of its fields (see `dict_field_names`) and of its groups (see `record_decl`) are
    /// chosen with it.
    pub fn dict_name(&mut self, tr: DefId) -> String {
        if let Some(n) = self.dict_names.get(&tr) {
            return n.clone();
        }
        let mut segs = vec![];
        if !tr.is_local() {
            segs.push(self.crate_of(tr));
        }
        segs.extend(self.path_segments(tr));
        segs.push("dict".into());
        let methods = self.dict_methods(tr);
        let parents = self.dict_parents(tr);
        let nfields = methods.len() + parents.len();
        let n = self.unique_global_with(names::type_name(&segs), |n| record_group_names(n, nfields));
        self.dict_names.insert(tr, n.clone());
        self.dict_traits.push(tr);
        let fields = self.dict_field_names(&n, &methods, &parents);
        self.dict_fields.insert(tr, fields);
        n
    }

    /// The field names of the dictionaries named `name`, by method (of `methods`, see
    /// `dict_methods`), and of the supertraits and associated type bounds `parents` (see
    /// `dict_parents`) in order: `name_<method>` and `name_super<k>_<trait>`, made unique among the
    /// HOL names (two method names may be one identifier, e.g. `f` and `f_`, see
    /// `names::ident_chars`). They are chosen in this order when the trait's dictionaries are first
    /// named, so they do not depend on the order of the uses of its fields.
    fn dict_field_names(&mut self, name: &str, methods: &[DefId], parents: &[ty::TraitRef<'tcx>]) -> (HashMap<DefId, String>, Vec<String>) {
        let tcx = self.tcx;
        let ms = methods
            .iter()
            .map(|&m| (m, self.unique_global(format!("{}_{}", name, names::ident_chars(tcx.item_name(m).as_str())))))
            .collect();
        let ps = parents
            .iter()
            .enumerate()
            .map(|(k, p)| self.unique_global(format!("{}_super{}_{}", name, k, names::ident_chars(tcx.item_name(p.def_id).as_str()))))
            .collect();
        (ms, ps)
    }

    /// The field of the dictionaries of `tr` holding the method `m` (one of `dict_methods`).
    pub fn dict_field(&mut self, tr: DefId, m: DefId) -> String {
        self.dict_name(tr);
        self.dict_fields[&tr].0.get(&m).expect("the method is a field of the dictionaries").clone()
    }

    /// The field of the dictionaries of `tr` holding the dictionary of its `k`-th supertrait or
    /// associated type bound (see `dict_parents`).
    pub fn dict_parent_field(&mut self, tr: DefId, k: usize) -> String {
        self.dict_name(tr);
        self.dict_fields[&tr].1[k].clone()
    }

    /// The HOL type of the dictionaries for the trait reference `r` (normalised in `env`).
    pub fn dict_type(&mut self, r: ty::TraitRef<'tcx>, env: ty::TypingEnv<'tcx>) -> String {
        let tcx = self.tcx;
        let n = self.dict_name(r.def_id);
        let mut a: Vec<String> = BASE_TVARS.iter().map(|s| s.to_string()).collect();
        for t in r.args.types() {
            a.push(self.ty(t));
        }
        for s in self.dict_slots(r) {
            let s = crate::frontend::normalize(tcx, env, ty::Unnormalized::new_wip(s));
            a.push(self.ty(s));
        }
        format!("({}) {}", a.join(", "), n)
    }

    /// The trait bounds of the generic item `owner` (with those of its parents) that are
    /// dictionary parameters, in order: those by traits with dictionaries, on types with generic
    /// parameters.
    pub fn dict_bounds(&self, owner: DefId) -> Vec<ty::TraitRef<'tcx>> {
        let tcx = self.tcx;
        let mut out: Vec<ty::TraitRef<'tcx>> = vec![];
        let ident = ty::GenericArgs::identity_for_item(tcx, owner);
        for c in tcx.clauses_of(owner).instantiate(tcx, ident).clauses {
            let Some(p) = c.skip_normalization().as_trait_clause() else { continue };
            // a higher-ranked bound (`for<'a> &'a T: Neg`) at erased regions, as the bounds it
            // proves are at a call
            let p = tcx.instantiate_bound_regions_with_erased(p);
            if p.polarity != ty::ClausePolarity::Positive || !self.has_dict(p.def_id()) {
                continue;
            }
            let r = tcx.erase_and_anonymize_regions(p.trait_ref);
            if r.args.has_param() && !out.contains(&r) {
                out.push(r);
            }
        }
        out
    }

    /// The bounds of the method `m` of its own (its `where` clauses, not those of its trait or
    /// implementation) that are dictionary parameters (as in `dict_bounds`). A dictionary field of
    /// a trait method takes them before the method's arguments (see `dict_decl`), as Aeneas's
    /// method clauses.
    pub fn own_dict_bounds(&self, m: DefId) -> Vec<ty::TraitRef<'tcx>> {
        if let Some(bs) = self.own_dict_bounds_memo.borrow().get(&m) {
            return bs.clone();
        }
        let bs = self.find_own_dict_bounds(m);
        self.own_dict_bounds_memo.borrow_mut().insert(m, bs.clone());
        bs
    }

    fn find_own_dict_bounds(&self, m: DefId) -> Vec<ty::TraitRef<'tcx>> {
        let tcx = self.tcx;
        let mut out: Vec<ty::TraitRef<'tcx>> = vec![];
        for (c, _) in tcx.clauses_of(m).instantiate_own_identity() {
            let Some(p) = c.skip_normalization().as_trait_clause() else { continue };
            let p = tcx.instantiate_bound_regions_with_erased(p);
            if p.polarity != ty::ClausePolarity::Positive || !self.has_dict(p.def_id()) {
                continue;
            }
            let r = tcx.erase_and_anonymize_regions(p.trait_ref);
            if r.args.has_param() && !out.contains(&r) {
                out.push(r);
            }
        }
        out
    }

    /// The dictionary parameters of the translation `key`, with their names: the bounds (see
    /// `dict_bounds`) of a generic item, or of the implementation of a default method's copy and
    /// the method's own bounds (see `own_dict_bounds`) there; an instance has none.
    pub fn dict_params(&self, key: FnKey<'tcx>) -> Vec<(ty::TraitRef<'tcx>, String)> {
        let tcx = self.tcx;
        let bounds = match key.1 {
            Inst::Generic => self.dict_bounds(key.0),
            Inst::ImplCopy(imp) => {
                let mut bs = self.dict_bounds(imp);
                let at = self.inst_args(key).expect("a copy has the arguments of its implementation");
                // (those still on types with generic parameters, as in `dict_bounds`)
                for b in self.own_dict_bounds(key.0) {
                    let b = tcx.erase_and_anonymize_regions(ty::EarlyBinder::bind(tcx, b).instantiate(tcx, at).skip_normalization());
                    if b.args.has_param() && !bs.contains(&b) {
                        bs.push(b);
                    }
                }
                bs
            }
            Inst::Mono(_) => return vec![],
        };
        bounds
            .into_iter()
            .enumerate()
            .map(|(k, r)| {
                let n = format!("d{}_{}", k, names::ident_chars(self.tcx.item_name(r.def_id).as_str()));
                (r, n)
            })
            .collect()
    }

    /// The HOL function types of the type parameters of the generic item `owner` bounded by an
    /// `Fn` trait (by index): a value of such a parameter is a function value (as a closure is),
    /// of the type its bound states (`F: Fn(u32) -> bool` is `32 word ⇒ (.., bool, ..) function_body`).
    pub fn fn_param_types(&mut self, owner: DefId) -> HashMap<u32, String> {
        let tcx = self.tcx;
        let mut out = HashMap::new();
        for (index, ins, ret) in self.fn_bounded_params(owner) {
            let norm = |t: Ty<'tcx>| {
                let t = tcx.erase_and_anonymize_regions(t);
                crate::frontend::normalize(tcx, ty::TypingEnv::post_analysis(tcx, owner), ty::Unnormalized::new_wip(t))
            };
            let ps: Vec<String> = ins.iter().map(|t| self.ty(norm(*t))).collect();
            let r = self.ty(norm(ret));
            out.insert(index, self.fun_type(&ps, &r));
        }
        out
    }

    /// The type parameters of the generic item `owner` bounded by an `Fn` trait: their indices,
    /// with the argument types and the result type their bounds state.
    pub fn fn_bounded_params(&self, owner: DefId) -> Vec<(u32, Vec<Ty<'tcx>>, Ty<'tcx>)> {
        let tcx = self.tcx;
        let ident = ty::GenericArgs::identity_for_item(tcx, owner);
        let clauses: Vec<ty::Clause<'tcx>> =
            tcx.clauses_of(owner).instantiate(tcx, ident).clauses.into_iter().map(|c| c.skip_normalization()).collect();
        let output = tcx.lang_items().fn_once_output();
        let mut out: Vec<(u32, Vec<Ty<'tcx>>, Ty<'tcx>)> = vec![];
        for c in &clauses {
            let Some(p) = c.as_trait_clause() else { continue };
            let p = tcx.instantiate_bound_regions_with_erased(p);
            if !self.is_fn_trait(p.def_id()) {
                continue;
            }
            let ty::Param(param) = *p.self_ty().kind() else { continue };
            let ty::Tuple(ins) = *p.trait_ref.args.type_at(1).kind() else { continue };
            if out.iter().any(|(i, _, _)| *i == param.index) {
                continue;
            }
            let ret = clauses
                .iter()
                .filter_map(|c| c.as_projection_clause())
                .map(|q| tcx.instantiate_bound_regions_with_erased(q))
                .find(|q| Some(q.projection_term.expect_projection_def_id().into()) == output && q.self_ty() == p.self_ty())
                .and_then(|q| q.term.as_type());
            let Some(ret) = ret else { continue };
            out.push((param.index, ins.iter().collect(), ret));
        }
        out
    }

    /// The datatypes of the dictionaries used, each after those of its supertraits.
    pub fn dict_decls(&mut self) -> String {
        let tcx = self.tcx;
        let mut out = String::new();
        let mut done: Vec<DefId> = vec![];
        let mut k = 0;
        // declaring one may use (and register) others: iterate until all are declared
        while k < self.dict_traits.len() {
            let mut order = vec![];
            self.dict_order(self.dict_traits[k], &mut done, &mut order);
            for tr in order {
                let d = self.dict_decl(tr);
                writeln!(out, "(* Rust: dictionaries of the trait {} *)", tcx.def_path_str(tr)).unwrap();
                out.push_str(&record_decl(&d.name, &d.tparams, &d.fields));
            }
            k += 1;
        }
        out
    }

    fn dict_order(&mut self, tr: DefId, done: &mut Vec<DefId>, order: &mut Vec<DefId>) {
        if done.contains(&tr) {
            return;
        }
        done.push(tr);
        // the datatypes of the dictionaries in its fields first: of its supertraits and associated
        // type bounds, and of its methods' own bounds
        for p in self.dict_parents(tr) {
            self.dict_order(p.def_id, done, order);
        }
        for m in self.dict_methods(tr) {
            for b in self.own_dict_bounds(m) {
                self.dict_order(b.def_id, done, order);
            }
        }
        order.push(tr);
    }

    /// The datatype of the dictionaries of `tr`: its trait parameters (`Self` first) are type
    /// variables, as are its slots (see `dict_slots`).
    fn dict_decl(&mut self, tr: DefId) -> DictDecl {
        let tcx = self.tcx;
        let name = self.dict_name(tr);
        let ident = ty::TraitRef::identity(tcx, tr);
        let mut tparams: Vec<String> = BASE_TVARS.iter().map(|s| s.to_string()).collect();
        for t in ident.args.types() {
            tparams.push(self.ty(t));
        }
        let slots = self.dict_slots(ident);
        let slot_vars: Vec<String> = (0..slots.len()).map(|i| format!("'slot{}", i)).collect();
        tparams.extend(slot_vars.iter().cloned());
        let saved = self.proj_tvars.take();
        let map: HashMap<ty::AliasTy<'tcx>, String> = slots
            .iter()
            .zip(slot_vars.iter())
            .map(|(s, v)| (self.proj_key(*s).expect("slots are projections"), v.clone()))
            .collect();
        self.proj_tvars = Some(map);
        let saved_env = self.proj_env.take();
        let mut fields = vec![];
        for m in self.dict_methods(tr) {
            let sig = self.sig_types(m);
            let (out, ins) = sig.split_last().expect("a signature has an output");
            let menv = ty::TypingEnv::post_analysis(tcx, m);
            // the projections that the datatypes of ADTs take, normalised as `field_projections`
            // finds them among the slots
            self.proj_env = Some(menv);
            let ps: Vec<String> = ins.iter().map(|t| self.ty(tcx.erase_and_anonymize_regions(*t))).collect();
            let ret = self.ty(tcx.erase_and_anonymize_regions(*out));
            let f = self.dict_field(tr, m);
            let mut t = String::new();
            for b in self.own_dict_bounds(m) {
                t.push_str(&format!("{} \\<Rightarrow> ", paren_ty(&self.dict_type(b, menv))));
            }
            t.push_str(&self.fun_type(&ps, &ret));
            fields.push((f, t));
        }
        let env = ty::TypingEnv::post_analysis(tcx, tr);
        // (the projections that the datatypes of ADTs take, normalised as `param_slots` finds them)
        self.proj_env = Some(env);
        for (k, p) in self.dict_parents(tr).into_iter().enumerate() {
            let f = self.dict_parent_field(tr, k);
            let t = self.dict_type(p, env);
            fields.push((f, t));
        }
        (self.proj_tvars, self.proj_env) = (saved, saved_env);
        DictDecl { name, fields, tparams }
    }
}
