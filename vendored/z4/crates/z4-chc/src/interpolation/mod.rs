// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolation-based lemma learning for PDR/Spacer
//!
//! This module implements interpolating SAT solving for CHC problems.
//! When A ∧ B is UNSAT, we compute an interpolant I such that:
//! - A ⊨ I (I is implied by A)
//! - I ∧ B is UNSAT (I is inconsistent with B)
//! - I uses only variables shared between A and B
//!
//! This is the core technique from Golem/Spacer for learning more general
//! blocking lemmas than point-based blocking.
//!
//! ## Implementation
//!
//! Currently uses Farkas-based interpolation for linear arithmetic.
//! Future: integrate with proof-producing SMT solver for richer interpolants.

use crate::farkas::compute_interpolant as farkas_interpolant;
use crate::ChcExpr;
use rustc_hash::FxHashSet;
use tracing::{debug, info};

pub(crate) mod core_ite_farkas;
mod fallback;
mod heuristics;
pub(crate) mod mbp_interpolation;
use fallback::{
    compute_unsat_core_interpolant, interpolate_with_disjunction_split, is_valid_interpolant,
};
use heuristics::{compute_bound_interpolant, compute_transitivity_interpolant};

/// Maximum total branches explored during disjunction-split interpolation.
/// Prevents exponential blowup from nested disjunctions (k^n for n disjunctions
/// with k disjuncts each). Each branch invokes a full SMT solve, so this bounds
/// the worst-case cost. Exceeding the limit triggers Unknown (sound fallback).
const DISJUNCTION_SPLIT_BRANCH_LIMIT: usize = 32;

/// Result of interpolant computation
#[derive(Debug, Clone)]
pub(crate) enum InterpolatingSatResult {
    /// A ∧ B is unsatisfiable, with interpolant
    Unsat(ChcExpr),
    /// Unknown (could not determine)
    Unknown,
}

#[inline]
fn debug_assert_shared_var_locality(
    _interpolant: &ChcExpr,
    _shared_vars: &FxHashSet<String>,
    _strategy: &'static str,
) {
    #[cfg(debug_assertions)]
    {
        let non_shared: Vec<String> = _interpolant
            .vars()
            .into_iter()
            .map(|v| v.name)
            .filter(|name| !_shared_vars.contains(name))
            .collect();
        debug_assert!(
            non_shared.is_empty(),
            "BUG: strategy {_strategy} produced interpolant with non-shared vars: {non_shared:?}"
        );
    }
}

/// Compute an interpolant from constraint lists.
///
/// When A (transition constraints) ∧ B (bad state) is UNSAT, compute an
/// interpolant I such that:
/// - A ⊨ I
/// - I ∧ B is UNSAT
/// - I uses only variables shared between A and B
///
/// REQUIRES: `shared_vars` contains exactly the variables that appear in both
///   `a_constraints` and `b_constraints` (the "interface" variables).
///
/// ENSURES: If `InterpolatingSatResult::Unsat(I)` is returned:
///   - `∧a_constraints ⊨ I` (A implies I, soundness of interpolant)
///   - `I ∧ ∧b_constraints` is UNSAT (I blocks B)
///   - `I` mentions only variables in `shared_vars` (locality property)
///
/// ENSURES: `InterpolatingSatResult::Unknown` is returned if:
///   - Either constraint list is empty, OR
///   - No interpolation technique could find a valid interpolant, OR
///   - Candidate interpolants fail Craig property validation
///     (This is NOT an error - caller should fall back to other methods)
pub(crate) fn interpolating_sat_constraints(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> InterpolatingSatResult {
    let mut budget = DISJUNCTION_SPLIT_BRANCH_LIMIT;
    interpolating_sat_constraints_with_budget(
        a_constraints,
        b_constraints,
        shared_vars,
        &mut budget,
    )
}

/// Budget-aware interpolation. The `branch_budget` tracks how many disjunction
/// branches remain across the entire recursive call tree. When exhausted,
/// disjunction splitting returns Unknown (sound: only affects completeness).
fn interpolating_sat_constraints_with_budget(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    branch_budget: &mut usize,
) -> InterpolatingSatResult {
    if a_constraints.is_empty() || b_constraints.is_empty() {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "precheck",
            reason = "empty_constraints",
            a_constraints = a_constraints.len(),
            b_constraints = b_constraints.len(),
            "Interpolation skipped: one side had no constraints",
        );
        return InterpolatingSatResult::Unknown;
    }

    debug!(
        event = "chc_interpolation_start",
        a_constraints = a_constraints.len(),
        b_constraints = b_constraints.len(),
        shared_vars = shared_vars.len(),
        branch_budget = *branch_budget,
        "Starting interpolation cascade",
    );

    // Try Farkas-based interpolation first
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "farkas",
        "Trying Farkas interpolation",
    );
    if let Some(interpolant) = farkas_interpolant(a_constraints, b_constraints, shared_vars) {
        if is_valid_interpolant(a_constraints, b_constraints, &interpolant, shared_vars) {
            debug_assert_shared_var_locality(&interpolant, shared_vars, "farkas");
            info!(
                event = "chc_interpolation_strategy_succeeded",
                strategy = "farkas",
                "Interpolation succeeded with Farkas strategy",
            );
            return InterpolatingSatResult::Unsat(interpolant);
        }
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "farkas",
            reason = "craig_validation_failed",
            "Farkas produced a candidate interpolant that failed Craig validation",
        );
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "farkas",
            reason = "no_candidate",
            "Farkas interpolation produced no candidate",
        );
    }

    // Try bound-based interpolation
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "bound",
        "Trying bound interpolation",
    );
    if let Some(interpolant) = compute_bound_interpolant(a_constraints, b_constraints, shared_vars)
    {
        if is_valid_interpolant(a_constraints, b_constraints, &interpolant, shared_vars) {
            debug_assert_shared_var_locality(&interpolant, shared_vars, "bound");
            info!(
                event = "chc_interpolation_strategy_succeeded",
                strategy = "bound",
                "Interpolation succeeded with bound strategy",
            );
            return InterpolatingSatResult::Unsat(interpolant);
        }
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "bound",
            reason = "craig_validation_failed",
            "Bound strategy produced a candidate interpolant that failed Craig validation",
        );
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "bound",
            reason = "no_candidate",
            "Bound interpolation produced no candidate",
        );
    }

    // Try transitivity-based interpolation
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "transitivity",
        "Trying transitivity interpolation",
    );
    if let Some(interpolant) =
        compute_transitivity_interpolant(a_constraints, b_constraints, shared_vars)
    {
        if is_valid_interpolant(a_constraints, b_constraints, &interpolant, shared_vars) {
            debug_assert_shared_var_locality(&interpolant, shared_vars, "transitivity");
            info!(
                event = "chc_interpolation_strategy_succeeded",
                strategy = "transitivity",
                "Interpolation succeeded with transitivity strategy",
            );
            return InterpolatingSatResult::Unsat(interpolant);
        }
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "transitivity",
            reason = "craig_validation_failed",
            "Transitivity strategy produced a candidate interpolant that failed Craig validation",
        );
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "transitivity",
            reason = "no_candidate",
            "Transitivity interpolation produced no candidate",
        );
    }

    // D11: Core-guided ITE-normalized Farkas interpolation.
    // When pure-LIA strategies fail because of ITE terms, case-split on ITE
    // conditions so each case becomes pure LIA, then delegate to Farkas.
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "ite_farkas",
        "Trying ITE-normalized Farkas interpolation (D11)",
    );
    if let Some(interpolant) =
        core_ite_farkas::compute_ite_farkas_interpolant(a_constraints, b_constraints, shared_vars)
    {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "ite_farkas");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "ite_farkas",
            "Interpolation succeeded with ITE-normalized Farkas (D11)",
        );
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "ite_farkas",
        reason = "no_candidate",
        "ITE-normalized Farkas interpolation produced no candidate",
    );

    // Dual MBP interpolation: when heuristic methods fail on mixed Bool+LIA,
    // use model-based projection to compute interpolants from B-partition models.
    // Placed before UNSAT-core: at TPA power 1+, UNSAT-core echoes previous
    // interpolants (shared-only conjuncts) and succeeds weakly, preventing MBP
    // from running. MBP produces fresh projections at every power level. (D10)
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "dual_mbp",
        "Trying dual MBP interpolation for mixed Bool+LIA",
    );
    if let Some(interpolant) =
        mbp_interpolation::compute_dual_mbp_interpolant(a_constraints, b_constraints, shared_vars)
    {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "dual_mbp");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "dual_mbp",
            "Interpolation succeeded with dual MBP strategy",
        );
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "dual_mbp",
        reason = "no_candidate",
        "Dual MBP interpolation produced no valid candidate",
    );

    // Fallback: UNSAT-core-based interpolation.
    // When heuristic methods fail, use the SMT solver's UNSAT core to extract
    // A-side constraints that conflict with B. Filter to shared-variable-only
    // conjuncts for a valid (though possibly weak) interpolant.
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "unsat_core",
        "Trying UNSAT-core interpolation fallback",
    );
    if let Some(interpolant) =
        compute_unsat_core_interpolant(a_constraints, b_constraints, shared_vars)
    {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "unsat_core");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "unsat_core",
            "Interpolation succeeded with UNSAT-core fallback",
        );
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "unsat_core",
        reason = "no_candidate",
        "UNSAT-core interpolation fallback produced no valid candidate",
    );

    // Disjunction case-splitting: if A contains top-level disjunctions,
    // split into cases and interpolate each branch separately.
    //
    // If A = A1 ∨ A2, and A ∧ B is UNSAT, then both A1 ∧ B and A2 ∧ B are UNSAT.
    // Get I1 from (A1, B) and I2 from (A2, B). Then I1 ∨ I2 is a valid interpolant:
    //   - A ⊨ I1 ∨ I2 (each disjunct implies its interpolant)
    //   - (I1 ∨ I2) ∧ B is UNSAT (both I1 ∧ B and I2 ∧ B are UNSAT)
    //   - Variable locality preserved (each Ii uses only shared vars)
    //
    // This enables k-to-1-inductive conversion where build_formula produces
    // Init(x_k) ∨ (Inv ∧ Trans) disjunctions (#2753).
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "disjunction_split",
        branch_budget = *branch_budget,
        "Trying disjunction-split interpolation fallback",
    );
    if let Some(result) =
        interpolate_with_disjunction_split(a_constraints, b_constraints, shared_vars, branch_budget)
    {
        match result {
            InterpolatingSatResult::Unsat(interpolant) => {
                debug_assert_shared_var_locality(&interpolant, shared_vars, "disjunction_split");
                info!(
                    event = "chc_interpolation_strategy_succeeded",
                    strategy = "disjunction_split",
                    "Interpolation succeeded with disjunction-split fallback",
                );
                return InterpolatingSatResult::Unsat(interpolant);
            }
            InterpolatingSatResult::Unknown => {
                info!(
                    event = "chc_interpolation_strategy_failed",
                    strategy = "disjunction_split",
                    reason = "branch_failure_or_budget_exhausted_or_invalid_combination",
                    "Disjunction-split interpolation failed",
                );
            }
        }
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "disjunction_split",
            reason = "no_disjunction",
            "Disjunction-split interpolation not applicable",
        );
    }

    info!(
        event = "chc_interpolation_unknown",
        a_constraints = a_constraints.len(),
        b_constraints = b_constraints.len(),
        shared_vars = shared_vars.len(),
        remaining_branch_budget = *branch_budget,
        "All interpolation strategies failed",
    );
    InterpolatingSatResult::Unknown
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
