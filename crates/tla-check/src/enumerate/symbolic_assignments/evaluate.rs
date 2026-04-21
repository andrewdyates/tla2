// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Evaluation of symbolic assignments into concrete primed-variable values.
//!
//! Handles progressive next-state context construction, conflict detection,
//! and InSet constraint management.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::Ordering as AtomicOrdering;
use std::sync::Arc;
use rustc_hash::FxHashSet;

use tla_eval::tir::TirProgram;

use crate::error::EvalError;
use crate::eval::{eval_iter_set_tlc_normalized, Env, EvalCtx};
use crate::Value;

use super::super::tir_leaf::eval_leaf;

use super::super::{
    debug_enum, expr_references_primed_vars, profile_enum_detail, PrimedAssignment,
    SymbolicAssignment, PROF_ASSIGN_US,
};
use super::toposort::topological_sort_assignments;

/// Result of checking a new value against existing constraints for a variable.
enum ValueConstraintResult {
    /// Value conflicts with existing constraint — no valid successors.
    Conflict,
    /// Value is redundant (same as existing constraint) — skip this assignment.
    Redundant,
    /// No conflict — proceed with the assignment.
    Ok,
}

/// Check if assigning `value` to `name` conflicts with existing constraints.
///
/// When constraint is `Some(existing_val)`: conflict if values differ, redundant if same.
/// When constraint is `None` (InSet): conflict if value not in pending_insets, otherwise
/// filters the InSet to just this value.
fn check_value_constraint(
    name: &Arc<str>,
    value: &Value,
    constraints: &HashMap<Arc<str>, Option<Value>>,
    pending_insets: &mut HashMap<Arc<str>, HashSet<Value>>,
    debug: bool,
    label: &str,
) -> ValueConstraintResult {
    let Some(existing) = constraints.get(name) else {
        return ValueConstraintResult::Ok;
    };
    let prefix = if label.is_empty() {
        String::new()
    } else {
        format!("{label} ")
    };
    match existing {
        Some(existing_val) => {
            if existing_val != value {
                if debug {
                    eprintln!(
                        "evaluate_symbolic_assignments: CONFLICT {prefix}{name}' = {value} vs existing {existing_val}"
                    );
                }
                ValueConstraintResult::Conflict
            } else {
                ValueConstraintResult::Redundant
            }
        }
        None => {
            // Was InSet, now constrained to specific value — filter InSet
            // Part of #2370 (E2): O(1) HashSet::contains instead of O(n) Vec::contains.
            if let Some(inset_values) = pending_insets.get_mut(name) {
                if !inset_values.contains(value) {
                    if debug {
                        eprintln!(
                            "evaluate_symbolic_assignments: CONFLICT {prefix}{name}' = {value} not in InSet {inset_values:?}"
                        );
                    }
                    return ValueConstraintResult::Conflict;
                }
                // Narrow InSet to single value
                inset_values.clear();
                inset_values.insert(value.clone());
            }
            ValueConstraintResult::Ok
        }
    }
}

/// Check if a new InSet for `name` conflicts with existing constraints.
///
/// Part of #2370 (E2): Takes and returns `HashSet<Value>` for O(1) membership
/// tests instead of O(n) Vec::contains. Intersection is also O(n+m) directly
/// on HashSets without temporary set construction.
///
/// Returns `Some(filtered_values)` on success, `None` on conflict.
#[allow(clippy::mutable_key_type)] // Value's AtomicU64 is for caching, not equality
fn check_inset_constraint(
    name: &Arc<str>,
    mut values: HashSet<Value>,
    constraints: &HashMap<Arc<str>, Option<Value>>,
    pending_insets: &HashMap<Arc<str>, HashSet<Value>>,
    debug: bool,
) -> Option<HashSet<Value>> {
    let Some(existing) = constraints.get(name) else {
        return Some(values);
    };
    match existing {
        Some(existing_val) => {
            // Part of #2370 (E2): O(1) HashSet::contains instead of O(n) Vec::contains.
            if !values.contains(existing_val) {
                if debug {
                    eprintln!(
                        "evaluate_symbolic_assignments: CONFLICT {name}' existing {existing_val} not in InSet {values:?}"
                    );
                }
                None // Conflict
            } else {
                // Existing value is in set — already constrained, skip adding InSet
                Some(HashSet::new()) // Empty signals "skip"
            }
        }
        None => {
            // Was already InSet, intersect directly via HashSet::retain — O(n).
            if let Some(prev_values) = pending_insets.get(name) {
                values.retain(|v| prev_values.contains(v));
                if values.is_empty() {
                    if debug {
                        eprintln!(
                            "evaluate_symbolic_assignments: CONFLICT {name}' InSet intersection empty"
                        );
                    }
                    return None; // Empty intersection
                }
            }
            Some(values)
        }
    }
}

/// Evaluate symbolic assignments with progressive next-state context
///
/// This handles TLA+ simultaneous assignment semantics by evaluating assignments
/// in order and making computed values available for subsequent expressions.
///
/// When an expression references primed variables from InSet assignments (x' \in S),
/// we defer evaluation until successor state building when we know the specific value.
///
/// **Conflict detection**: When the same variable receives multiple assignments from
/// different parts of a conjunction (e.g., `UNCHANGED hr` from NowNext and `hr' = 5`
/// from HCnxt), this function detects the conflict and returns an empty result,
/// indicating no valid successor states exist for this branch.
pub(in crate::enumerate) fn evaluate_symbolic_assignments(
    ctx: &EvalCtx,
    symbolic: &[SymbolicAssignment],
    tir: Option<&TirProgram<'_>>,
) -> Result<Vec<PrimedAssignment>, EvalError> {
    // Part of #2370 (E3): Use Arc<Env> instead of bare Env to avoid O(N) HashMap
    // clone per assignment. Before each eval, we Arc::clone (O(1) refcount bump)
    // into eval_ctx. After eval, we clear eval_ctx's reference and use
    // Arc::make_mut for in-place mutation (no clone when refcount == 1).
    let mut next_state: Arc<Env> = Arc::new(Env::new());
    let mut result = Vec::new();
    // Avoid cloning the entire EvalCtx (including local_stack) for every assignment.
    // We only need to update the next_state view as we compute primed values.
    let mut eval_ctx = ctx.clone();

    // Track which variables come from InSet (have multiple possible values)
    let mut inset_vars: FxHashSet<Arc<str>> = FxHashSet::default();

    // Track constraints for conflict detection:
    // - None: unconstrained
    // - Some(None): constrained to InSet (values tracked in pending_insets)
    // - Some(Some(v)): constrained to specific value
    let mut constraints: HashMap<Arc<str>, Option<Value>> = HashMap::new();

    // Part of #2370 (E2): Track pending InSet assignments as HashSet for O(1)
    // membership tests in check_value_constraint and check_inset_constraint.
    #[allow(clippy::mutable_key_type)] // Value's AtomicU64 is for caching, not equality
    let mut pending_insets: HashMap<Arc<str>, HashSet<Value>> = HashMap::new();

    // First pass: identify InSet variables
    for sym in symbolic {
        if let SymbolicAssignment::InSet(name, _, _) = sym {
            inset_vars.insert(name.clone());
        }
    }

    // Topological sort: ensure assignments that define x' come before expressions that reference x'.
    // This fixes the case where `announced' = (count' >= VT)` is extracted before `count' = count + 1`.
    // Pass ctx to follow operator references for hidden dependencies.
    let sorted_symbolic = topological_sort_assignments(Some(ctx), symbolic);

    let debug = debug_enum();

    for sym in &sorted_symbolic {
        match sym {
            SymbolicAssignment::Expr(name, expr, bindings) => {
                // Check if this expression references any primed InSet variables
                let refs_inset = expr_references_primed_vars(ctx, &expr.node, &inset_vars);
                if refs_inset {
                    if debug {
                        eprintln!(
                            "evaluate_symbolic_assignments: deferring {name}' (references InSet primed vars)"
                        );
                    }
                    // Can't evaluate now - will be evaluated per-combination
                    result.push(PrimedAssignment::DeferredExpr(name.clone(), expr.clone()));
                } else {
                    // Part of #2370 (E3): Share next_state Arc with eval_ctx via
                    // O(1) refcount bump instead of O(N) HashMap clone.
                    // Part of #3460: always use the same context construction path
                    // regardless of TIR presence. The previous tir.is_some() branch
                    // used with_next_state_for_eval_scope() which calls
                    // clear_for_eval_scope_boundary() — a GLOBAL cache clear that
                    // broke evaluation state between primed assignments even when TIR
                    // never evaluated any expression (all fell back to AST).
                    *eval_ctx.next_state_mut() = Some(Arc::clone(&next_state));
                    let binding_ctx = eval_ctx.with_captured_bindings(bindings);
                    let value = if profile_enum_detail() {
                        let start = std::time::Instant::now();
                        let res = eval_leaf(&binding_ctx, expr, tir);
                        PROF_ASSIGN_US
                            .fetch_add(start.elapsed().as_micros() as u64, AtomicOrdering::Relaxed);
                        res?
                    } else {
                        eval_leaf(&binding_ctx, expr, tir)?
                    };
                    // Drop eval_ctx's Arc reference so next_state has refcount 1,
                    // enabling in-place mutation via Arc::make_mut below.
                    drop(binding_ctx);
                    *eval_ctx.next_state_mut() = None;

                    match check_value_constraint(
                        name,
                        &value,
                        &constraints,
                        &mut pending_insets,
                        debug,
                        "",
                    ) {
                        ValueConstraintResult::Conflict => return Ok(Vec::new()),
                        ValueConstraintResult::Redundant => continue,
                        ValueConstraintResult::Ok => {}
                    }
                    constraints.insert(name.clone(), Some(value.clone()));
                    // Part of #3964: Use Arc::get_mut (non-atomic fast path) when
                    // refcount == 1, falling back to Arc::make_mut only when shared.
                    // After dropping eval_ctx's reference above, next_state is
                    // typically the sole owner.
                    if let Some(env) = Arc::get_mut(&mut next_state) {
                        env.insert(name.clone(), value.clone());
                    } else {
                        Arc::make_mut(&mut next_state).insert(name.clone(), value.clone());
                    }
                    result.push(PrimedAssignment::Assign(name.clone(), value));
                }
            }
            SymbolicAssignment::Value(name, value) => {
                match check_value_constraint(
                    name,
                    value,
                    &constraints,
                    &mut pending_insets,
                    debug,
                    "",
                ) {
                    ValueConstraintResult::Conflict => return Ok(Vec::new()),
                    ValueConstraintResult::Redundant => continue,
                    ValueConstraintResult::Ok => {}
                }
                constraints.insert(name.clone(), Some(value.clone()));
                // Part of #3964: Use Arc::get_mut for non-atomic fast path.
                if let Some(env) = Arc::get_mut(&mut next_state) {
                    env.insert(name.clone(), value.clone());
                } else {
                    Arc::make_mut(&mut next_state).insert(name.clone(), value.clone());
                }
                result.push(PrimedAssignment::Assign(name.clone(), value.clone()));
            }
            SymbolicAssignment::Unchanged(name) => {
                // UNCHANGED x means x' = x
                // BUG FIX #1102: Use lookup_state_var which checks state_env (array path)
                // first, then falls back to env (HashMap). Previously only checked env,
                // so when state vars were bound via bind_state_array (sequential BFS),
                // UNCHANGED vars silently produced no successor.
                //
                // Part of #3354: Emit Assign instead of Unchanged so the diff builder
                // sees the actual current value. When current_values differs from the
                // base ArrayState (parallel worker split-array mode), PrimedAssignment::
                // Unchanged is silently dropped by the diff builder (build_diff.rs),
                // producing empty diffs instead of the correct override value.
                if let Some(current) = ctx.lookup_state_var(name) {
                    match check_value_constraint(
                        name,
                        &current,
                        &constraints,
                        &mut pending_insets,
                        debug,
                        "UNCHANGED",
                    ) {
                        ValueConstraintResult::Conflict => return Ok(Vec::new()),
                        ValueConstraintResult::Redundant => continue,
                        ValueConstraintResult::Ok => {}
                    }
                    constraints.insert(name.clone(), Some(current.clone()));
                    // Part of #3964: Use Arc::get_mut for non-atomic fast path.
                    if let Some(env) = Arc::get_mut(&mut next_state) {
                        env.insert(name.clone(), current.clone());
                    } else {
                        Arc::make_mut(&mut next_state).insert(name.clone(), current.clone());
                    }
                    result.push(PrimedAssignment::Assign(name.clone(), current));
                }
            }
            SymbolicAssignment::InSet(name, set_expr, bindings) => {
                // Part of #3460: always use the same context construction path
                // regardless of TIR presence. See Expr branch above for rationale.
                *eval_ctx.next_state_mut() = Some(Arc::clone(&next_state));
                let binding_ctx = eval_ctx.with_captured_bindings(bindings);
                let set_val = if profile_enum_detail() {
                    let start = std::time::Instant::now();
                    let res = eval_leaf(&binding_ctx, set_expr, tir);
                    PROF_ASSIGN_US
                        .fetch_add(start.elapsed().as_micros() as u64, AtomicOrdering::Relaxed);
                    res?
                } else {
                    eval_leaf(&binding_ctx, set_expr, tir)?
                };
                // Part of #1828: use eval_iter_set for SetPred-aware iteration.
                // Part of #2987: use TLC-normalized ordering for consistency
                // (order-independent here since we collect into HashSet).
                #[allow(clippy::mutable_key_type)]
                let iter_result: Result<HashSet<Value>, _> =
                    eval_iter_set_tlc_normalized(&binding_ctx, &set_val, Some(set_expr.span))
                        .map(std::iter::Iterator::collect);
                let set_type_name = set_val.type_name();
                // Part of #2370 (E3): Drop eval_ctx's Arc reference so next_state
                // has refcount 1 for subsequent iterations that mutate it.
                drop(binding_ctx);
                *eval_ctx.next_state_mut() = None;

                match iter_result {
                    Ok(values) => {
                        match check_inset_constraint(
                            name,
                            values,
                            &constraints,
                            &pending_insets,
                            debug,
                        ) {
                            None => return Ok(Vec::new()),              // Conflict
                            Some(filtered) if filtered.is_empty() => {} // Already constrained, skip
                            Some(filtered) => {
                                constraints.insert(name.clone(), None); // Mark as InSet-constrained
                                pending_insets.insert(name.clone(), filtered);
                            }
                        }
                    }
                    // Part of #1433: replace bare Err(_) with explicit classification.
                    // Only the canonical "not enumerable" TypeError should reconstruct
                    // as a disabled-action signal. All other errors (SetPred internal
                    // failures, etc.) propagate as-is to avoid masking real faults.
                    Err(e)
                        if matches!(
                            &e,
                            EvalError::TypeError {
                                expected: "Set",
                                ..
                            }
                        ) =>
                    {
                        // RHS is not a set - type error disables action (TLC semantics)
                        // Part of #166: When x' \in non_set, the action is disabled
                        if debug {
                            eprintln!(
                                "evaluate_symbolic_assignments: {}' \\in non-set ({}), action disabled",
                                name,
                                set_type_name
                            );
                        }
                        return Err(EvalError::TypeError {
                            expected: "Set",
                            got: set_type_name,
                            span: Some(set_expr.span),
                        });
                    }
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
        }
    }

    // Finalize pending InSets - add them to result.
    // Convert HashSet to Vec for PrimedAssignment::InSet.
    // Part of #263: Sort by variable name for deterministic iteration order.
    // HashMap iteration order depends on RandomState seed, causing non-deterministic
    // successor generation and state count variance across runs.
    let mut pending_insets_sorted: Vec<_> = pending_insets.into_iter().collect();
    pending_insets_sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (name, values) in pending_insets_sorted {
        if values.len() == 1 {
            // Single value - convert to Assign
            let value = values.into_iter().next().expect("checked len == 1");
            // Part of #3964: Use Arc::get_mut for non-atomic fast path.
            if let Some(env) = Arc::get_mut(&mut next_state) {
                env.insert(name.clone(), value.clone());
            } else {
                Arc::make_mut(&mut next_state).insert(name.clone(), value.clone());
            }
            result.push(PrimedAssignment::Assign(name.clone(), value));
        } else if !values.is_empty() {
            let mut values_vec: Vec<Value> = values.into_iter().collect();
            values_vec.sort();
            result.push(PrimedAssignment::InSet(name, values_vec));
        }
    }

    Ok(result)
}
