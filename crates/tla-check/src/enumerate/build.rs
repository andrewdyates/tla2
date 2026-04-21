// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test-only module (gated behind #[cfg(test)] in enumerate.rs).

use crate::error::EvalError;
use crate::eval::{eval_entry, EvalCtx};
use crate::state::ArrayState;
use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;
use std::convert::Infallible;
use std::ops::ControlFlow;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

use super::emitter::{FullStateEmitter, SuccessorEmitter};
use super::{debug_enum, PrimedAssignment};

/// Generate all combinations of InSet values
pub(super) fn generate_inset_combinations(
    inset_vars: &[(Arc<str>, Vec<Value>)],
) -> Vec<Vec<(Arc<str>, Value)>> {
    if inset_vars.is_empty() {
        return vec![vec![]]; // One empty combination if no InSet vars
    }

    let mut combinations = vec![vec![]];

    for (name, values) in inset_vars {
        let mut new_combinations = Vec::new();
        for combo in &combinations {
            for value in values {
                let mut new_combo = combo.clone();
                new_combo.push((name.clone(), value.clone()));
                new_combinations.push(new_combo);
            }
        }
        combinations = new_combinations;
    }

    combinations
}

/// Unified deferred-successor builder used by state, array, and diff outputs.
pub(super) fn build_successors_with_deferred<E: SuccessorEmitter>(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
    ctx: &EvalCtx,
    debug_prefix: &str,
    emitter: &mut E,
) -> Result<ControlFlow<E::Halt, ()>, EvalError> {
    use crate::eval::Env;

    let indexed_vars = index_vars(vars, registry);

    // Separate InSet assignments (which produce combinations) from others.
    let mut inset_vars: Vec<(Arc<str>, Vec<Value>)> = Vec::new();
    let mut deferred: Vec<(Arc<str>, Spanned<Expr>)> = Vec::new();
    let mut fixed_assignments: Vec<(Arc<str>, Value)> = Vec::new();
    let mut unchanged_vars: Vec<Arc<str>> = Vec::new();

    for assignment in assignments {
        match assignment {
            PrimedAssignment::Assign(name, value) => {
                fixed_assignments.push((name.clone(), value.clone()));
            }
            PrimedAssignment::Unchanged(name) => {
                unchanged_vars.push(name.clone());
            }
            PrimedAssignment::InSet(name, values) => {
                if values.is_empty() {
                    return Ok(ControlFlow::Continue(()));
                }
                inset_vars.push((name.clone(), values.clone()));
            }
            PrimedAssignment::DeferredExpr(name, expr) => {
                deferred.push((name.clone(), expr.clone()));
            }
        }
    }

    let combinations = generate_inset_combinations(&inset_vars);
    let debug = debug_enum();

    for combo in combinations {
        let mut next_state: Env = Env::new();

        for (name, value) in &fixed_assignments {
            next_state.insert(name.clone(), value.clone());
        }

        for name in &unchanged_vars {
            if let Some(idx) = registry.get(name.as_ref()) {
                next_state.insert(name.clone(), current_array.get(idx).clone());
            }
        }

        for (name, value) in &combo {
            next_state.insert(name.clone(), value.clone());
        }

        let mut eval_ctx = ctx.clone();
        *eval_ctx.next_state_mut() = Some(Arc::new(next_state.clone()));

        // Part of #2380: Propagate deferred expression errors instead of swallowing.
        // Fix #1552 established that TLC propagates ALL errors from getNextStates
        // fatally — there is no "skip this combination" semantic for eval errors.
        for (name, expr) in &deferred {
            let value = eval_entry(&eval_ctx, expr)?;
            if debug {
                eprintln!("{debug_prefix}: {}' = {}", name, value);
            }
            next_state.insert(name.clone(), value);
            *eval_ctx.next_state_mut() = Some(Arc::new(next_state.clone()));
        }

        let mut working = current_array.clone();
        for (name, idx) in &indexed_vars {
            if let Some(value) = next_state.get(name) {
                working.set(*idx, value.clone());
            }
        }

        if let ControlFlow::Break(halt) = emitter.emit(current_array, &working, registry)? {
            return Ok(ControlFlow::Break(halt));
        }
    }
    Ok(ControlFlow::Continue(()))
}

fn index_vars(vars: &[Arc<str>], registry: &VarRegistry) -> Vec<(Arc<str>, VarIndex)> {
    let mut indexed = Vec::with_capacity(vars.len());
    for var in vars {
        if let Some(idx) = registry.get(var.as_ref()) {
            indexed.push((Arc::clone(var), idx));
        }
    }
    indexed
}

/// Convert PrimedAssignments to an indexed assignment map, returning `None`
/// if any InSet domain is empty (no successors). Shared preprocessing for
/// all non-deferred emitter-based combination paths.
fn prepare_assignment_map(
    num_vars: usize,
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
) -> Option<Vec<Option<Vec<Value>>>> {
    let mut assignment_map: Vec<Option<Vec<Value>>> = vec![None; num_vars];
    for assignment in assignments {
        match assignment {
            PrimedAssignment::Assign(name, value) => {
                if let Some(idx) = registry.get(name) {
                    assignment_map[idx.as_usize()] = Some(vec![value.clone()]);
                }
            }
            PrimedAssignment::Unchanged(_) => {}
            PrimedAssignment::InSet(name, values) => {
                if let Some(idx) = registry.get(name) {
                    assignment_map[idx.as_usize()] = Some(values.clone());
                }
            }
            PrimedAssignment::DeferredExpr(_, _) => {
                unreachable!(
                    "DeferredExpr should be handled by build_successor_states_with_deferred"
                )
            }
        }
    }
    if assignment_map
        .iter()
        .any(|v| matches!(v, Some(vals) if vals.is_empty()))
    {
        return None;
    }
    Some(assignment_map)
}

/// Compute incremental fingerprint heuristic and combination count from an
/// assignment map. Returns `(use_incremental_fp, num_combinations)`.
fn assignment_map_stats(assignment_map: &[Option<Vec<Value>>]) -> (bool, usize) {
    let num_vars = assignment_map.len();
    let assigned_vars = assignment_map.iter().filter(|v| v.is_some()).count();
    let use_incremental_fp = assigned_vars < num_vars;
    let num_combinations = assignment_map.iter().fold(1usize, |acc, v| {
        acc.saturating_mul(v.as_ref().map_or(1, std::vec::Vec::len))
    });
    (use_incremental_fp, num_combinations)
}

/// Propagate `EvalError` from an infallible-halt emitter pipeline.
///
/// The `Infallible` halt type guarantees the `Break` branch is unreachable.
/// Unlike the previous `expect_infallible_continue`, this propagates errors
/// via `?` instead of panicking, matching TLC's `EvalException` propagation
/// at the `doNext`/`doModel` call boundary.
///
/// Part of #2380: replace `.expect()` with proper error propagation.
#[inline]
fn propagate_infallible_continue(
    result: Result<ControlFlow<Infallible, ()>, EvalError>,
) -> Result<(), EvalError> {
    match result? {
        ControlFlow::Continue(()) => Ok(()),
        ControlFlow::Break(never) => match never {},
    }
}

/// Build successor ArrayStates from an existing ArrayState (avoids State conversion)
pub fn build_successor_array_states_from_array(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
) -> Result<Vec<ArrayState>, EvalError> {
    let assignment_map = match prepare_assignment_map(vars.len(), assignments, registry) {
        Some(m) => m,
        None => return Ok(Vec::new()),
    };

    let (use_incremental_fp, num_combinations) = assignment_map_stats(&assignment_map);

    let mut results = Vec::with_capacity(num_combinations);
    let mut array_state = current_array.clone();
    if use_incremental_fp {
        array_state.ensure_fp_cache_with_value_fps(registry);
    }
    let mut emitter = FullStateEmitter::new(&mut results, !use_incremental_fp);
    propagate_infallible_continue(enumerate_combinations(
        &assignment_map,
        0,
        current_array,
        &mut array_state,
        registry,
        use_incremental_fp,
        &mut emitter,
    ))?;
    Ok(results)
}

/// Unified combination enumeration with emitter-based output.
///
/// Walks the assignment map recursively, mutating `array_state` in place. At
/// each leaf (all variables assigned), calls `emitter.emit(base, array_state, registry)`.
/// The emitter controls what happens: clone to Vec<ArrayState>, validate guards
/// before cloning, compute diffs, etc.
///
/// When `use_incremental_fp` is true, uses `set_with_registry` for incremental
/// fingerprint updates during assignment; otherwise uses plain `set`.
pub(super) fn enumerate_combinations<E: SuccessorEmitter>(
    assignment_map: &[Option<Vec<Value>>],
    idx: usize,
    base: &ArrayState,
    array_state: &mut ArrayState,
    registry: &VarRegistry,
    use_incremental_fp: bool,
    emitter: &mut E,
) -> Result<ControlFlow<E::Halt, ()>, EvalError> {
    if idx == assignment_map.len() {
        return emitter.emit(base, array_state, registry);
    }

    let var_idx = VarIndex::new(idx);
    match &assignment_map[idx] {
        Some(values) => {
            for val in values {
                if use_incremental_fp {
                    array_state.set_with_registry(var_idx, val.clone(), registry);
                } else {
                    array_state.set(var_idx, val.clone());
                }
                if let ControlFlow::Break(halt) = enumerate_combinations(
                    assignment_map,
                    idx + 1,
                    base,
                    array_state,
                    registry,
                    use_incremental_fp,
                    emitter,
                )? {
                    return Ok(ControlFlow::Break(halt));
                }
            }
        }
        None => {
            if let ControlFlow::Break(halt) = enumerate_combinations(
                assignment_map,
                idx + 1,
                base,
                array_state,
                registry,
                use_incremental_fp,
                emitter,
            )? {
                return Ok(ControlFlow::Break(halt));
            }
        }
    }
    Ok(ControlFlow::Continue(()))
}

/// Build successor ArrayStates with optional context for deferred expression evaluation
///
/// When `ctx` is provided and there are `DeferredExpr` assignments, they will be
/// evaluated for each InSet combination with the appropriate next-state context.
pub fn build_successor_array_states_with_ctx(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
    ctx: Option<&EvalCtx>,
) -> Result<Vec<ArrayState>, EvalError> {
    // Check if we have any deferred expressions that need evaluation
    let has_deferred = assignments
        .iter()
        .any(|a| matches!(a, PrimedAssignment::DeferredExpr(_, _)));

    if has_deferred {
        if let Some(ctx) = ctx {
            // Slow path: need to evaluate deferred expressions per-combination
            return build_successor_array_states_with_deferred(
                current_array,
                vars,
                assignments,
                registry,
                ctx,
            );
        }
    }

    // Fast path: no deferred expressions, use existing implementation
    build_successor_array_states_from_array(current_array, vars, assignments, registry)
}

/// Build successor ArrayStates when there are DeferredExpr assignments.
///
/// For each combination of InSet values, creates a next-state context and evaluates
/// any deferred expressions before building the final ArrayState.
fn build_successor_array_states_with_deferred(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
    ctx: &EvalCtx,
) -> Result<Vec<ArrayState>, EvalError> {
    let mut results = Vec::new();
    let mut emitter = FullStateEmitter::new(&mut results, true);
    propagate_infallible_continue(build_successors_with_deferred(
        current_array,
        vars,
        assignments,
        registry,
        ctx,
        "build_successor_array_states_with_deferred",
        &mut emitter,
    ))?;
    Ok(results)
}

#[cfg(test)]
#[path = "build_tests/mod.rs"]
mod tests;
