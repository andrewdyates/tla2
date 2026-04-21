// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Safety classification and tautology detection for PROPERTY entries.
//!
//! Part of #2740: provides the three-way classification (state invariant,
//! action implied, temporal) and pre-BFS tautology detection shared by
//! both the sequential and parallel checker paths.

use crate::check::CheckError;
use crate::eval::EvalCtx;
use crate::liveness::{AstToLive, LiveExpr};
use rustc_hash::FxHashMap;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::Spanned;

use super::property_plan::contains_enabled_standalone;
use super::{
    contains_temporal_standalone, flatten_and_terms_standalone, plan_property_terms,
    PlannedPropertyTerm,
};
use crate::LivenessCheckError;

// ---------------------------------------------------------------------------
// Tautology detection — canonical function shared by sequential and parallel.
//
// Part of #2740: eliminates duplicated `is_trivially_unsatisfiable()` definitions
// in check/model_checker/liveness.rs and parallel/checker/liveness.rs.
// ---------------------------------------------------------------------------

/// Check if a LiveExpr formula is trivially unsatisfiable (tautology detection).
///
/// Used for TLC_LIVE_FORMULA_TAUTOLOGY detection (EC 2253): if the negation
/// of a liveness property is trivially unsatisfiable, the property is a tautology.
/// Detects patterns like `Bool(false)`, `Always(Bool(false))`, `Eventually(Bool(false))`,
/// and conjunctions containing any trivially unsatisfiable term.
///
/// Both the sequential and parallel checker paths MUST use this function for all
/// tautology detection to prevent parity drift.
pub(crate) fn is_trivially_unsatisfiable(expr: &LiveExpr) -> bool {
    match expr {
        LiveExpr::Bool(false) => true,
        LiveExpr::Always(inner) | LiveExpr::Eventually(inner) => is_trivially_unsatisfiable(inner),
        LiveExpr::And(conjuncts) => conjuncts.iter().any(is_trivially_unsatisfiable),
        LiveExpr::Or(disjuncts) => disjuncts.iter().all(is_trivially_unsatisfiable),
        LiveExpr::Not(inner) => matches!(**inner, LiveExpr::Bool(true)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// PROPERTY safety classification — canonical function shared by both checkers.
//
// Part of #2740: the parallel checker was missing state-level PROPERTY promotion.
// This function provides the three-way classification that was previously only
// available on ModelChecker::classify_property_safety_parts.
// ---------------------------------------------------------------------------

pub(crate) struct PropertySafetyClassification {
    /// Canonical action-level PROPERTY checks evaluated via `eval_entry()`.
    pub eval_implied_actions: Vec<(String, Spanned<Expr>)>,
    /// Canonical state-level PROPERTY invariants evaluated via `eval_entry()`.
    pub eval_state_invariants: Vec<(String, Spanned<Expr>)>,
    /// Property names that contribute state-level `PROPERTY` checks during BFS.
    ///
    /// This is broader than `promoted_invariant_properties`: mixed
    /// `[]P /\ <>Q` properties still need PROPERTY attribution if `[]P` fails
    /// during BFS, even though the property is not fully promoted.
    pub state_violation_properties: Vec<String>,
    /// Init predicates: non-Always state/constant-level terms (e.g., `M!Init` in
    /// `M!Init /\ [][M!Next]_M!vars`). Checked against initial states only during BFS.
    /// Part of #2834: without this, properties with init terms are sent to the post-BFS
    /// safety_temporal pass, which iterates over ALL transitions with per-transition
    /// cache clearing — causing hangs for specs like EWD998PCal (2.4M transitions).
    pub init_predicates: Vec<(String, Spanned<Expr>)>,
    /// Properties whose ALL terms were state-level (fully promoted to invariants).
    pub promoted_invariant_properties: Vec<String>,
    /// Properties whose ALL terms were action-level (fully promoted to implied actions).
    pub promoted_action_properties: Vec<String>,
}

/// Classify PROPERTY entries into BFS-phase checking buckets (#2332, #2670, #2740).
///
/// Standalone version callable from both sequential and parallel checker setup.
/// Performs the three-way classification:
///
/// 1. **State-level invariants** (`[]P` where P is state/constant level):
///    Checked during BFS for unseen states only.
///
/// 2. **Implied actions** (`[]A` where A is action-level, no nested temporal):
///    Checked during BFS for ALL transitions.
///
/// 3. **Temporal** (WF, SF, <>P, etc.): Left for post-BFS liveness checking.
///
/// Also tracks which properties were *fully* promoted (all terms extracted) so
/// the post-BFS liveness phase can skip them.
pub(crate) fn classify_property_safety_parts(
    ctx: &EvalCtx,
    properties: &[String],
    op_defs: &FxHashMap<String, OperatorDef>,
) -> PropertySafetyClassification {
    let mut eval_action_terms: Vec<(String, Spanned<Expr>)> = Vec::new();
    let mut eval_state_terms: Vec<(String, Spanned<Expr>)> = Vec::new();
    let mut state_violation_properties: Vec<String> = Vec::new();
    let mut init_preds: Vec<(String, Spanned<Expr>)> = Vec::new();
    let mut promoted_invariant_names: Vec<String> = Vec::new();
    let mut promoted_action_names: Vec<String> = Vec::new();

    for prop_name in properties {
        if let Some(plan) = plan_property_terms(ctx, op_defs, prop_name) {
            let property_name = plan.property;
            let mut state_term_bodies: Vec<Spanned<Expr>> = Vec::new();
            let mut action_term_bodies: Vec<Spanned<Expr>> = Vec::new();
            let mut eval_action_term_bodies: Vec<Spanned<Expr>> = Vec::new();
            let mut eval_state_term_bodies: Vec<Spanned<Expr>> = Vec::new();
            let mut init_term_bodies: Vec<Spanned<Expr>> = Vec::new();
            let mut has_non_safety_terms = false;

            for term in plan.terms {
                match term {
                    PlannedPropertyTerm::Init(body) => init_term_bodies.push(body),
                    PlannedPropertyTerm::StateCompiled(body) => state_term_bodies.push(body),
                    PlannedPropertyTerm::StateEval(body) => eval_state_term_bodies.push(body),
                    PlannedPropertyTerm::ActionCompiled(body) => action_term_bodies.push(body),
                    PlannedPropertyTerm::ActionEval(body) => eval_action_term_bodies.push(body),
                    PlannedPropertyTerm::Liveness(_) => has_non_safety_terms = true,
                }
            }

            // Part of #3354 Slice 2: route promoted state-level PROPERTY terms
            // through the canonical eval path instead of compiling a second guard IR.
            if !state_term_bodies.is_empty() {
                for body in &state_term_bodies {
                    eval_state_terms.push((prop_name.clone(), body.clone()));
                }
                if !state_violation_properties.contains(prop_name) {
                    state_violation_properties.push(prop_name.clone());
                }
                // Only mark as fully promoted if no other terms remain
                if action_term_bodies.is_empty()
                    && init_term_bodies.is_empty()
                    && !has_non_safety_terms
                {
                    promoted_invariant_names.push(prop_name.clone());
                }
            }

            // Part of #3354 Slice 2: route promoted action-level PROPERTY terms
            // through the canonical eval path instead of compiling a fast-path guard.
            if !action_term_bodies.is_empty() {
                for body in &action_term_bodies {
                    eval_action_terms.push((prop_name.clone(), body.clone()));
                }
            }

            // Collect eval-based action terms from ModuleRef properties (#2983).
            if !eval_action_term_bodies.is_empty() {
                for body in &eval_action_term_bodies {
                    eval_action_terms.push((prop_name.clone(), body.clone()));
                }
            }

            // Collect eval-based state invariants for ENABLED-containing terms (#3113).
            if !eval_state_term_bodies.is_empty() {
                for body in &eval_state_term_bodies {
                    eval_state_terms.push((prop_name.clone(), body.clone()));
                }
                if !state_violation_properties.contains(prop_name) {
                    state_violation_properties.push(prop_name.clone());
                }
            }

            // Collect init predicates (#2834)
            if !init_term_bodies.is_empty() {
                for body in &init_term_bodies {
                    init_preds.push((prop_name.clone(), body.clone()));
                }
            }

            // If a property has ALL terms handled (any combination of promoted
            // state/action eval terms and init predicates) and no liveness terms,
            // it's fully promoted.
            // Both promoted lists are used for the post-BFS liveness skip.
            let all_terms_handled = !has_non_safety_terms
                && (!state_term_bodies.is_empty()
                    || !action_term_bodies.is_empty()
                    || !eval_action_term_bodies.is_empty()
                    || !eval_state_term_bodies.is_empty()
                    || !init_term_bodies.is_empty());
            if all_terms_handled {
                if !promoted_invariant_names.contains(&property_name) {
                    promoted_invariant_names.push(property_name.clone());
                }
                if !promoted_action_names.contains(&property_name) {
                    promoted_action_names.push(property_name.clone());
                }
            }
        }
    }

    PropertySafetyClassification {
        eval_implied_actions: eval_action_terms,
        eval_state_invariants: eval_state_terms,
        state_violation_properties,
        init_predicates: init_preds,
        promoted_invariant_properties: promoted_invariant_names,
        promoted_action_properties: promoted_action_names,
    }
}

// ---------------------------------------------------------------------------
// Pre-BFS tautology detection — shared by both checker paths.
//
// Part of #2740: the parallel checker previously detected tautologies only
// after BFS completion, wasting the entire BFS run. This function enables
// pre-BFS detection matching the sequential checker's behavior.
// ---------------------------------------------------------------------------

/// Check if a conjunct term is a "liveness" term (needs post-BFS checking).
///
/// Approximates the sequential checker's `classify_term` logic in `safety_split.rs`:
/// - `Always(inner)` where inner has no temporal operators and no ENABLED -> safety
/// - `Eventually`, `LeadsTo`, `WeakFair`, `StrongFair` -> liveness
/// - Non-temporal, non-ENABLED terms -> safety (init predicates)
/// - Everything else -> liveness
///
/// **Known gap (P3):** Unlike `classify_term`, this function does NOT resolve
/// `Ident` references through operator definitions (no `classify_ident_term`
/// equivalent). Properties defined as named operator refs (e.g., `Liveness`
/// where `Liveness == <>TRUE`) will be classified by syntactic form only.
/// See test `tautology_via_operator_ref_known_gap`.
///
/// **Known gap (P3):** `ModuleRef` nodes are also not resolved — they fall
/// through to the catch-all and are classified by syntactic form. The sequential
/// checker handles these via `classify_module_ref_term` in `safety_split.rs:291`.
/// See test `is_liveness_conjunct_module_ref_known_gap`.
///
/// **Known gap (P2):** `contains_temporal_standalone` does not detect
/// `Apply(Ident("WF_xxx"), _)` / `Apply(Ident("SF_xxx"), _)` as temporal,
/// unlike the sequential `contains_temporal_helper`. The lowerer converts these
/// to native `WeakFair`/`StrongFair` nodes at parse time, but the Apply form
/// can arise from instance expansion. See test
/// `contains_temporal_standalone_misses_apply_wf_sf_known_gap`.
pub(crate) fn is_liveness_conjunct(expr: &Expr) -> bool {
    match expr {
        Expr::Always(inner) => {
            // []P is safety only if P has no nested temporal operators and no ENABLED.
            // Otherwise it's liveness (e.g., []<>P, [][ENABLED A => A']_v).
            contains_temporal_standalone(&inner.node) || contains_enabled_standalone(&inner.node)
        }
        Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::WeakFair(_, _)
        | Expr::StrongFair(_, _) => true,
        _ => {
            // Non-temporal terms are init predicates (safety). Terms with
            // temporal operators or ENABLED that aren't one of the above
            // forms are liveness.
            contains_temporal_standalone(expr) || contains_enabled_standalone(expr)
        }
    }
}

/// Check all PROPERTY entries for tautological liveness formulas before BFS.
///
/// TLC rejects tautological liveness properties before state exploration begins
/// (EC 2253). A property like `<>TRUE` negates to `[]FALSE`, which is trivially
/// unsatisfiable, meaning the property can never be violated — it's a tautology.
///
/// For mixed safety+liveness properties (e.g., `[]TypeOK /\ <>TRUE`), the
/// liveness terms are extracted first and only those are checked for tautology.
/// This matches the sequential checker's `check_properties_for_tautologies`
/// which calls `separate_safety_liveness_parts` before tautology analysis.
///
/// Returns `Some(CheckError)` on the first tautological property found, or `None`
/// if all properties are valid.
pub(crate) fn check_property_tautologies(
    ctx: &EvalCtx,
    properties: &[String],
    op_defs: &FxHashMap<String, OperatorDef>,
    root_module_name: &str,
) -> Option<CheckError> {
    if properties.is_empty() {
        return None;
    }

    let converter = AstToLive::new().with_location_module_name(root_module_name);

    for prop_name in properties {
        let def = match op_defs.get(prop_name) {
            Some(d) => d,
            None => continue, // Missing property errors are reported later
        };

        // Flatten the property into conjuncts and extract only liveness terms.
        // This matches the sequential checker's pre-separation via
        // separate_safety_liveness_parts before tautology checking.
        let mut terms = Vec::new();
        flatten_and_terms_standalone(&def.body, &mut terms);

        let liveness_terms: Vec<&Spanned<Expr>> = terms
            .iter()
            .filter(|t| is_liveness_conjunct(&t.node))
            .collect();

        if liveness_terms.is_empty() {
            continue; // Purely safety property, no liveness to check
        }

        // Reconjoin liveness terms for tautology analysis.
        let liveness_expr = if liveness_terms.len() == 1 {
            liveness_terms[0].clone()
        } else {
            let mut iter = liveness_terms.into_iter().cloned();
            let mut result = iter
                .next()
                .expect("invariant: liveness_terms has >= 2 elements");
            for term in iter {
                result = Spanned::new(Expr::And(Box::new(result), Box::new(term)), def.body.span);
            }
            result
        };

        // Convert the liveness portion to LiveExpr for tautology analysis.
        let prop_live = match converter.convert(ctx, &liveness_expr) {
            Ok(live) => live,
            Err(_e) => {
                // Part of #2793: Log conversion errors instead of silently skipping.
                // The actual error is re-reported during liveness checking, but logging
                // here makes the tautology-skip visible for debugging.
                debug_eprintln!(
                    crate::check::debug::tla2_debug(),
                    "[property-classify] skipping tautology check for '{}': conversion error: {}",
                    prop_name,
                    _e
                );
                continue;
            }
        };

        let negated = LiveExpr::not(prop_live).push_negation();
        if is_trivially_unsatisfiable(&negated) {
            return Some(
                LivenessCheckError::FormulaTautology {
                    property: prop_name.clone(),
                }
                .into(),
            );
        }
    }

    None
}
