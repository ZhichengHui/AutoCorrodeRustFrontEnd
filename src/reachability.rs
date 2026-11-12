//! The `match` arms rustc finds unreachable (covered by the preceding arms, the
//! `unreachable_patterns` lint): they are not translated. rustc's match checking (the query
//! `check_match`) is wrapped: after it, the arms of every `match` of the body are analysed again
//! with rustc's pattern analysis, while the body's THIR is still there (MIR building takes it).

use std::collections::HashSet;
use std::sync::{Mutex, OnceLock};

use rustc_arena::{DroplessArena, TypedArena};
use rustc_hir::HirId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::thir::{ExprId, ExprKind, Thir};
use rustc_middle::ty::{self, TyCtxt};
use rustc_pattern_analysis::MatchArm;
use rustc_pattern_analysis::rustc::{RustcPatCtxt, analyze_match};
use rustc_pattern_analysis::usefulness::Usefulness;
use rustc_span::ErrorGuaranteed;

type CheckMatch = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> Result<(), ErrorGuaranteed>;

static RUSTC_CHECK_MATCH: OnceLock<CheckMatch> = OnceLock::new();
static UNREACHABLE: Mutex<Option<HashSet<HirId>>> = Mutex::new(None);

/// To be called from `Callbacks::config`'s `override_queries`.
pub fn wrap_check_match(providers: &mut rustc_middle::util::Providers) {
    RUSTC_CHECK_MATCH.set(providers.queries.check_match).expect("check_match is wrapped once");
    providers.queries.check_match = check_match;
}

/// Is the `match` arm `arm` unreachable?
pub fn unreachable_arm(arm: HirId) -> bool {
    UNREACHABLE.lock().expect("unreachable arms").as_ref().is_some_and(|s| s.contains(&arm))
}

fn check_match(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
    let rustc = RUSTC_CHECK_MATCH.get().expect("check_match is wrapped");
    rustc(tcx, def_id)?;
    let (thir, _) = tcx.thir_body(def_id)?;
    let unreachable = unreachable_arms(tcx, def_id, &thir.borrow());
    UNREACHABLE.lock().expect("unreachable arms").get_or_insert_with(HashSet::new).extend(unreachable);
    Ok(())
}

/// The unreachable arms of the `match` expressions of the body `def_id`, as rustc's match
/// checking finds them.
fn unreachable_arms<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId, thir: &Thir<'tcx>) -> Vec<HirId> {
    let typeck_results = tcx.typeck(def_id);
    let hir_source = tcx.local_def_id_to_hir_id(def_id);
    let pattern_arena = TypedArena::default();
    let dropless_arena = DroplessArena::default();
    let mut out = vec![];
    for expr in thir.exprs.iter() {
        let ExprKind::Match { scrutinee, ref arms, .. } = expr.kind else { continue };
        let scrut = &thir[scrutinee];
        let cx = RustcPatCtxt {
            tcx,
            typeck_results,
            typing_env: ty::TypingEnv::post_typeck_until_borrowck_for_mir_build(tcx, def_id),
            module: tcx.parent_module(hir_source),
            dropless_arena: &dropless_arena,
            match_lint_level: hir_source,
            whole_match_span: Some(expr.span),
            scrut_span: scrut.span,
            refutable: true,
            known_valid_scrutinee: known_valid(thir, scrutinee),
            internal_state: Default::default(),
        };
        let mut tarms = vec![];
        for &arm in arms.iter() {
            let arm = &thir.arms[arm];
            // a pattern with errors: rustc reported them, there is no analysis
            if arm.pattern.pat_error_reported().is_err() {
                tarms.clear();
                break;
            }
            let pat = pattern_arena.alloc(cx.lower_pat(&arm.pattern));
            tarms.push(MatchArm { pat, arm_data: arm.hir_id, has_guard: arm.guard.is_some() });
        }
        if tarms.len() != arms.len() {
            continue;
        }
        let Ok(report) = analyze_match(&cx, &tarms, scrut.ty) else { continue };
        for (arm, usefulness) in report.arm_usefulness.iter() {
            if let Usefulness::Redundant(_) = usefulness {
                out.push(arm.arm_data);
            }
        }
    }
    out
}

/// Is the place of the scrutinee `e` known to hold a valid value (as rustc's match checking
/// decides it): not behind a dereference or in a union field.
fn known_valid(thir: &Thir<'_>, e: ExprId) -> bool {
    match thir[e].kind {
        ExprKind::Deref { .. } => false,
        ExprKind::Field { lhs, .. } => {
            !matches!(thir[lhs].ty.kind(), ty::Adt(def, _) if def.is_union()) && known_valid(thir, lhs)
        }
        ExprKind::Index { lhs, .. } => known_valid(thir, lhs),
        ExprKind::Scope { value, .. } => known_valid(thir, value),
        ExprKind::NeverToAny { source }
        | ExprKind::Cast { source }
        | ExprKind::ValueExpr { source }
        | ExprKind::PointerCoercion { source, .. }
        | ExprKind::PlaceTypeAscription { source, .. }
        | ExprKind::ValueTypeAscription { source, .. }
        | ExprKind::PlaceUnwrapUnsafeBinder { source }
        | ExprKind::ValueUnwrapUnsafeBinder { source }
        | ExprKind::WrapUnsafeBinder { source } => known_valid(thir, source),
        _ => true,
    }
}
