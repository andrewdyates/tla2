// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared test helpers for liveness checking tests.
//!
//! Consolidates duplicated helpers from checker/tests.rs, consistency.rs,
//! and tarjan.rs per #1337.

use crate::error::EvalResult;
use crate::eval::EvalCtx;
use crate::liveness::checker::{
    GroupedLivenessPlan, LivenessChecker, LivenessConstraints, PemPlan,
};
use crate::liveness::live_expr::LiveExpr;
use crate::liveness::tableau::Tableau;
use crate::state::State;
use crate::Value;
use tla_core::Spanned;

/// No-op successor function for tests that don't need state transitions.
/// Previously duplicated in checker/tests.rs and consistency.rs.
pub(crate) fn empty_successors(_: &State) -> EvalResult<Vec<State>> {
    Ok(Vec::new())
}

/// Create a simple state with a single variable `x` set to an integer.
/// Previously in tarjan.rs tests, inlined as `State::from_pairs` elsewhere.
pub(crate) fn make_state(x: i64) -> State {
    State::from_pairs([("x", Value::int(x))])
}

/// Wrap a value in a dummy span for test AST construction.
/// Previously duplicated in checker/tests.rs, ast_to_live/tests.rs,
/// init_strategy.rs, and z4_enumerate.rs.
pub(crate) fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

/// Create a LivenessChecker from a temporal formula with default context.
/// Replaces the 3-line Tableau::new + EvalCtx::new + LivenessChecker::new pattern
/// that appeared 18+ times in checker/tests.rs.
pub(crate) fn make_checker(formula: LiveExpr) -> LivenessChecker {
    let tableau = Tableau::new(formula);
    let ctx = EvalCtx::new();
    LivenessChecker::new(tableau, ctx)
}

/// Create a LivenessChecker with constraints and default context.
/// Replaces the 4-line Tableau::new + constraints + EvalCtx::new +
/// LivenessChecker::new_with_constraints pattern in checker/tests.rs.
pub(crate) fn make_checker_with_constraints(
    formula: LiveExpr,
    constraints: LivenessConstraints,
) -> LivenessChecker {
    let tableau = Tableau::new(formula);
    let ctx = EvalCtx::new();
    LivenessChecker::new_with_constraints(tableau, ctx, constraints)
}

/// Convert `LivenessConstraints` to a single-PEM `GroupedLivenessPlan`.
///
/// Constructs a plan where all AE/EA constraints map to a single PEM disjunct,
/// making it equivalent to the legacy `check_liveness()` code path. This allows
/// tests to exercise the production `check_liveness_grouped()` path instead of
/// the deleted non-grouped path. Part of #2718.
pub(crate) fn constraints_to_grouped_plan(
    constraints: &LivenessConstraints,
) -> GroupedLivenessPlan {
    let ae_state_count = constraints.ae_state.len();
    let ae_action_count = constraints.ae_action.len();

    let mut check_state = Vec::with_capacity(ae_state_count + constraints.ea_state.len());
    check_state.extend(constraints.ae_state.iter().cloned());
    check_state.extend(constraints.ea_state.iter().cloned());

    let mut check_action = Vec::with_capacity(ae_action_count + constraints.ea_action.len());
    check_action.extend(constraints.ae_action.iter().cloned());
    check_action.extend(constraints.ea_action.iter().cloned());

    let pem = PemPlan {
        ae_state_idx: (0..ae_state_count).collect(),
        ea_state_idx: (ae_state_count..check_state.len()).collect(),
        ae_action_idx: (0..ae_action_count).collect(),
        ea_action_idx: (ae_action_count..check_action.len()).collect(),
    };

    GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state,
        check_action,
        pems: vec![pem],
    }
}

/// Create a LivenessChecker with a populated VarRegistry.
///
/// Exercises the array-based fast path in eval_action_checks_batched
/// (`!registry_is_empty` branch), skipped by `make_checker`.
#[cfg(test)]
pub(crate) fn make_checker_with_vars(formula: LiveExpr, var_names: &[&str]) -> LivenessChecker {
    let tableau = Tableau::new(formula);
    let mut ctx = EvalCtx::new();
    ctx.register_vars(var_names.iter().map(|s| (*s).to_string()));
    LivenessChecker::new(tableau, ctx)
}
