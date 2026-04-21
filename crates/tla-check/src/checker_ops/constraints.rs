// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constraint and terminal state checking.
//!
//! Part of #2565: canonical constraint evaluation functions shared by both
//! the sequential and parallel checker paths.
//! Part of #2484: canonical terminal state checking.

use crate::check::CheckError;
use crate::config::TerminalSpec;
use crate::eval::EvalCtx;
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use crate::Value;
use crate::{ConfigCheckError, EvalCheckError};

/// Evaluate a single constraint operator, requiring a boolean result.
///
/// This is the **canonical** leaf constraint evaluation function. All constraint
/// evaluation across sequential and parallel paths MUST route through this
/// function to prevent drift in error-mapping semantics.
///
/// TLC alignment: mirrors `Tool.isInModel()` / `Tool.isInActions()` boolean check.
///
/// Part of #2565: unifies duplicated `eval_op` + match-on-bool patterns.
pub(crate) fn eval_constraint_bool(
    ctx: &mut EvalCtx,
    constraint_name: &str,
) -> Result<bool, CheckError> {
    match ctx.eval_op(constraint_name) {
        Ok(Value::Bool(true)) => Ok(true),
        Ok(Value::Bool(false)) => Ok(false),
        Ok(_) => Err(EvalCheckError::ConstraintNotBoolean(constraint_name.to_string()).into()),
        Err(e) => Err(EvalCheckError::Eval(e).into()),
    }
}

/// Evaluate all constraints in the currently bound scope, short-circuiting
/// on first `false`.
///
/// Assumes the evaluation scope is already set up by the caller. For state
/// constraints, the successor state must be bound; for action constraints,
/// both current state and next_state must be set.
///
/// Part of #2565: canonical constraint loop shared by all checker paths.
pub(crate) fn check_constraints_in_bound_scope(
    ctx: &mut EvalCtx,
    constraints: &[String],
) -> Result<bool, CheckError> {
    for constraint_name in constraints {
        if !eval_constraint_bool(ctx, constraint_name)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Check CONSTRAINT predicates against an `ArrayState`.
///
/// Binds the array state via RAII guard and evaluates all constraints.
/// Used for initial state filtering in both sequential and parallel paths.
///
/// Part of #2565: canonical ArrayState constraint check.
pub(crate) fn check_state_constraints_array(
    ctx: &mut EvalCtx,
    constraints: &[String],
    array_state: &ArrayState,
) -> Result<bool, CheckError> {
    if constraints.is_empty() {
        return Ok(true);
    }
    let _state_guard = ctx.bind_state_env_guard(array_state.env_ref());
    // Part of #3458/#3465: Establish array-bound eval boundary before constraint
    // evaluation to prevent stale INSTANCE-scoped cache leaks across states.
    crate::eval::clear_for_bound_state_eval_scope(ctx);
    check_constraints_in_bound_scope(ctx, constraints)
}

/// Check ACTION_CONSTRAINT predicates for a transition using `ArrayState`.
///
/// Binds current state variables (unprimed) via `state_env` and successor
/// state variables (primed) via `next_state_env`, both using RAII guards.
///
/// Part of #2484: canonical ArrayState action constraint check.
pub(crate) fn check_action_constraints_array(
    ctx: &mut EvalCtx,
    action_constraints: &[String],
    current_array: &ArrayState,
    succ_array: &ArrayState,
) -> Result<bool, CheckError> {
    if action_constraints.is_empty() {
        return Ok(true);
    }
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let _next_guard = ctx.bind_next_state_env_guard(succ_array.env_ref());
    // Part of #3458/#3465: Establish array-bound eval boundary before action
    // constraint evaluation to prevent stale cache leaks across transitions.
    crate::eval::clear_for_bound_state_eval_scope(ctx);
    check_constraints_in_bound_scope(ctx, action_constraints)
}

/// Check both CONSTRAINT and ACTION_CONSTRAINT for a successor using `ArrayState`.
///
/// Handles the complete constraint-checking contract for a transition from
/// `current_array` to `succ_array`:
/// 1. Evaluate state constraints with `succ_array` variables bound
/// 2. Evaluate action constraints with `current_array` (unprimed) and
///    `succ_array` (primed)
///
/// Returns `false` if any constraint is unsatisfied, `true` if all pass.
///
/// TLC alignment: mirrors `Worker.addElement()` -> `tool.isInModel(succState)`
/// which checks both constraint types in a single call.
///
/// Part of #2484: ArrayState version of `check_constraints_for_successor`.
pub(crate) fn check_constraints_for_successor_array(
    ctx: &mut EvalCtx,
    state_constraints: &[String],
    action_constraints: &[String],
    current_array: &ArrayState,
    succ_array: &ArrayState,
) -> Result<bool, CheckError> {
    if !check_state_constraints_array(ctx, state_constraints, succ_array)? {
        return Ok(false);
    }
    check_action_constraints_array(ctx, action_constraints, current_array, succ_array)
}

// ---------------------------------------------------------------------------
// Terminal state checking — canonical functions shared by sequential and parallel.
//
// Part of #2484: unifies 3 separate terminal-checking implementations
// (check_terminal_array free function, is_terminal_state, is_terminal_state_array)
// into canonical functions callable from both checker paths.
// ---------------------------------------------------------------------------

/// Check if an `ArrayState` is a terminal state.
///
/// Terminal states are intentional end points (e.g., "SAT" in a SAT solver spec)
/// and should NOT be reported as deadlocks. Returns `false` if `terminal` is `None`.
///
/// This is the **canonical** ArrayState terminal check used by both the sequential
/// (`ModelChecker::is_terminal_state_array`) and parallel
/// (`check_terminal_array`) checker paths. Both paths MUST call this function
/// to prevent parity drift.
///
/// Part of #2484: replaces duplicated terminal-checking logic in `invariants/eval.rs`.
pub(crate) fn check_terminal_array_state(
    ctx: &mut EvalCtx,
    terminal: Option<&TerminalSpec>,
    var_registry: &VarRegistry,
    array_state: &ArrayState,
) -> Result<bool, CheckError> {
    let Some(terminal) = terminal else {
        return Ok(false);
    };

    match terminal {
        TerminalSpec::Predicates(preds) => {
            for (var_name, expected_val_str) in preds {
                if let Some(idx) = var_registry.get(var_name) {
                    let actual_val = array_state.get(idx);
                    let expected_val = crate::constants::parse_constant_value(
                        expected_val_str.as_str(),
                    )
                    .map_err(|e| {
                        ConfigCheckError::Config(format!(
                            "TERMINAL predicate for '{}': cannot parse value '{}': {}",
                            var_name, expected_val_str, e
                        ))
                    })?;
                    if actual_val == expected_val {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }
        TerminalSpec::Operator(op_name) => {
            let _state_guard = ctx.bind_state_env_guard(array_state.env_ref());
            // Part of #3458/#3465: Establish array-bound eval boundary before
            // terminal operator evaluation.
            crate::eval::clear_for_bound_state_eval_scope(ctx);
            eval_constraint_bool(ctx, op_name)
        }
    }
}
