//! Trait dictionaries (dictionary passing, as in Aeneas).
//!
//! A trait is a HOL datatype with one field per method (a uRust function value) and one per
//! supertrait (the supertrait's dictionary); an implementation is a value of it. A generic item
//! takes one dictionary parameter per trait bound of its signature, and a call in its body
//! resolved to a bound calls the field of the bound's dictionary. The associated types of a
//! trait, and those of its supertraits, are type parameters of its datatype ("slots").

use std::collections::HashMap;
use std::fmt::Write as _;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TypeVisitableExt};

use crate::frontend::{FnKey, Frontend, Inst};
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

impl<'tcx> Frontend<'tcx> {
    /// `Fn`, `FnMut`, `FnOnce`: a bound by one of them is the function value itself.
    pub fn is_fn_trait(&self, tr: DefId) -> bool {
        self.tcx.fn_trait_kind_from_def_id(tr).is_some()
    }

    /// The methods of `tr` that are fields of its dictionaries: those without type parameters of
    /// their own (a field cannot be polymorphic: HOL has no rank-2 types).
    pub fn dict_methods(&self, tr: DefId) -> Vec<DefId> {
        self.tcx
            .associated_items(tr)
            .in_definition_order()
            .filter(|i| i.is_fn())
            .filter(|i| {
                let c = self.tcx.generics_of(i.def_id).own_counts();
                c.types == 0 && c.consts == 0
            })
            .map(|i| i.def_id)
            .collect()
    }

    /// The supertraits of `tr` (bounds on `Self`) and the bounds of its associated types (e.g.
    /// `<Self as IntoIterator>::IntoIter: Iterator`), as trait references on its own generic
    /// parameters, with whether each is a supertrait.
    fn trait_bounds(&self, tr: DefId) -> Vec<(ty::TraitRef<'tcx>, bool)> {
        let tcx = self.tcx;
        let mut clauses: Vec<(ty::Clause<'tcx>, bool)> =
            tcx.explicit_super_clauses_of(tr).skip_binder().iter().map(|(c, _)| (*c, true)).collect();
        for i in tcx.associated_items(tr).in_definition_order() {
            if matches!(i.kind, ty::AssocKind::Type { .. }) && tcx.generics_of(i.def_id).own_params.is_empty() {
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

    /// Does a bound by `tr` take a dictionary: does it have a method field or a supertrait with a
    /// dictionary (`Fn` bounds are function values instead)?
    pub fn has_dict(&self, tr: DefId) -> bool {
        if self.is_fn_trait(tr) {
            return false;
        }
        !self.dict_methods(tr).is_empty() || !self.dict_parents(tr).is_empty()
    }

    /// The associated types of a trait reference that its dictionary datatype takes as type
    /// parameters: its trait's own (without generic parameters of their own), then those of its
    /// supertraits with dictionaries, in order.
    pub fn dict_slots(&self, r: ty::TraitRef<'tcx>) -> Vec<Ty<'tcx>> {
        let tcx = self.tcx;
        let mut out: Vec<Ty<'tcx>> = tcx
            .associated_items(r.def_id)
            .in_definition_order()
            .filter(|i| matches!(i.kind, ty::AssocKind::Type { .. }) && tcx.generics_of(i.def_id).own_counts().types == 0)
            .map(|i| {
                let own = tcx.generics_of(i.def_id).own_params.len();
                let args = tcx.mk_args_from_iter(
                    r.args.iter().chain((0..own).map(|_| tcx.lifetimes.re_erased.into())),
                );
                Ty::new_projection(tcx, ty::IsRigid::No, i.def_id, args)
            })
            .collect();
        for p in self.dict_parents(r.def_id) {
            let pr = ty::EarlyBinder::bind(tcx, p).instantiate(tcx, r.args).skip_normalization();
            out.extend(self.dict_slots(pr));
        }
        out
    }

    /// The HOL name of the dictionary datatype of `tr` (also the name of its constructor).
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
        let n = self.unique_global(names::type_name(&segs));
        self.dict_names.insert(tr, n.clone());
        self.dict_traits.push(tr);
        n
    }

    /// The field of the dictionaries of `tr` holding the method `m`.
    pub fn dict_field(&mut self, tr: DefId, m: DefId) -> String {
        format!("{}_{}", self.dict_name(tr), names::ident_chars(self.tcx.item_name(m).as_str()))
    }

    /// The field of the dictionaries of `tr` holding the dictionary of its `k`-th supertrait or
    /// associated type bound (see `dict_parents`).
    pub fn dict_parent_field(&mut self, tr: DefId, k: usize) -> String {
        let p = self.dict_parents(tr)[k].def_id;
        format!("{}_super{}_{}", self.dict_name(tr), k, names::ident_chars(self.tcx.item_name(p).as_str()))
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
            let s = tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(s)).unwrap_or(s);
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

    /// The dictionary parameters of the translation `key`, with their names: the bounds (see
    /// `dict_bounds`) of a generic item, or of the implementation of a default method's copy; an
    /// instance has none.
    pub fn dict_params(&self, key: FnKey<'tcx>) -> Vec<(ty::TraitRef<'tcx>, String)> {
        let owner = match key.1 {
            Inst::Generic => key.0,
            Inst::ImplCopy(imp) => imp,
            Inst::Mono(_) => return vec![],
        };
        self.dict_bounds(owner)
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
        let ident = ty::GenericArgs::identity_for_item(tcx, owner);
        let clauses: Vec<ty::Clause<'tcx>> =
            tcx.clauses_of(owner).instantiate(tcx, ident).clauses.into_iter().map(|c| c.skip_normalization()).collect();
        let output = tcx.lang_items().fn_once_output();
        let mut out = HashMap::new();
        for c in &clauses {
            let Some(p) = c.as_trait_clause() else { continue };
            let p = tcx.instantiate_bound_regions_with_erased(p);
            if !self.is_fn_trait(p.def_id()) {
                continue;
            }
            let ty::Param(param) = *p.self_ty().kind() else { continue };
            let ty::Tuple(ins) = *p.trait_ref.args.type_at(1).kind() else { continue };
            if out.contains_key(&param.index) {
                continue;
            }
            let ret = clauses
                .iter()
                .filter_map(|c| c.as_projection_clause())
                .map(|q| tcx.instantiate_bound_regions_with_erased(q))
                .find(|q| Some(q.projection_term.expect_projection_def_id().into()) == output && q.self_ty() == p.self_ty())
                .and_then(|q| q.term.as_type());
            let Some(ret) = ret else { continue };
            let ps: Vec<String> = ins.iter().map(|t| self.ty(tcx.erase_and_anonymize_regions(t))).collect();
            let r = self.ty(tcx.erase_and_anonymize_regions(ret));
            out.insert(param.index, self.fun_type(&ps, &r));
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
                let fields: Vec<String> =
                    d.fields.iter().map(|(f, t)| format!("({}: \\<open>{}\\<close>)", f, t)).collect();
                writeln!(out, "datatype ({}) {} =\n  {} {}\n", d.tparams.join(", "), d.name, d.name, fields.join("\n    ")).unwrap();
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
        for p in self.dict_parents(tr) {
            self.dict_order(p.def_id, done, order);
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
            .filter_map(|(s, v)| match s.kind() {
                ty::Alias(_, a) => Some((*a, v.clone())),
                _ => None,
            })
            .collect();
        self.proj_tvars = Some(map);
        let mut fields = vec![];
        for m in self.dict_methods(tr) {
            let sig = tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(m).instantiate_identity().skip_normalization());
            let ps: Vec<String> = sig.inputs().iter().map(|t| self.ty(tcx.erase_and_anonymize_regions(*t))).collect();
            let ret = self.ty(tcx.erase_and_anonymize_regions(sig.output()));
            let f = self.dict_field(tr, m);
            fields.push((f, self.fun_type(&ps, &ret)));
        }
        let env = ty::TypingEnv::post_analysis(tcx, tr);
        for (k, p) in self.dict_parents(tr).into_iter().enumerate() {
            let f = self.dict_parent_field(tr, k);
            let t = self.dict_type(p, env);
            fields.push((f, t));
        }
        self.proj_tvars = saved;
        DictDecl { name, fields, tparams }
    }
}
