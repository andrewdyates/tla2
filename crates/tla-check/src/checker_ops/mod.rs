// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared operational helpers for the sequential and parallel model checkers.
//!
//! Both checker paths (sequential in `check/model_checker/` and parallel in `parallel/`)
//! implement the same model-checking algorithm. This module centralizes leaf operations
//! that must behave identically across both paths to prevent parity drift.
//!
//! Part of #2056: eliminates duplicated depth-to-level conversion and storage fault
//! conversion logic that had diverged between the two paths.

mod action_constraint_analysis;
mod constraints;
mod fairness;
mod instance_qualify;
mod invariants;
pub(crate) mod pc_dispatch;
mod prepare;
mod property_classify;
mod property_plan;
mod safety_temporal;
mod trace_actions;

pub(crate) use action_constraint_analysis::*;
pub(crate) use constraints::*;
pub(crate) use fairness::*;
pub(crate) use invariants::*;
pub(crate) use prepare::*;
pub(crate) use property_classify::*;
pub(crate) use property_plan::{plan_property_terms, PlannedPropertyTerm};
pub use safety_temporal::any_property_requires_liveness_checker;
pub(crate) use safety_temporal::{
    classify_safety_temporal, eval_property_bool_term, eval_property_bool_term_to_result,
    SafetyTemporalClassification,
};
pub(crate) use trace_actions::{identify_action_labels, ActionLabelCtx};

use crate::check::CheckError;
use crate::check::{expr_contains, CheckStats, ScanDecision};
use crate::eval::EvalCtx;
use crate::eval::TlcRuntimeStats;
use crate::state::{value_fingerprint, Fingerprint, State};
use crate::storage::{FingerprintSet, StorageFault};
use crate::{ConfigCheckError, InfraCheckError, RuntimeCheckError};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{NameId, Spanned};

// Part of #2740: compile_implied_actions_from_properties removed.
// Superseded by classify_property_safety_parts which handles both state-level
// and action-level classification. The old function only extracted action-level
// guards, missing state-level PROPERTY promotion.

/// Flatten nested `And` expressions into a list of conjuncts.
/// Standalone version of `ModelChecker::flatten_and_terms`.
pub(crate) fn flatten_and_terms_standalone(expr: &Spanned<Expr>, out: &mut Vec<Spanned<Expr>>) {
    match &expr.node {
        Expr::And(a, b) => {
            flatten_and_terms_standalone(a, out);
            flatten_and_terms_standalone(b, out);
        }
        _ => out.push(expr.clone()),
    }
}

/// Check if an expression contains nested temporal operators.
///
/// Delegates to `expr_contains` from `temporal_scan.rs` — the single exhaustive
/// scanner over all `Expr` variants. This prevents the incomplete-copy bug class
/// where ad-hoc scanners miss operators nested inside `If`, `Let`, `Case`,
/// `FuncApply`, quantifiers, records, etc. (see #2680).
///
/// Uses the `SafetyTemporalFastPath` predicate:
/// - `ENABLED` is treated as temporal (conservative for safety classification)
/// - `Ident` is not treated as temporal (semantic safety net via `get_level_with_ctx`)
pub(crate) fn contains_temporal_standalone(expr: &Expr) -> bool {
    expr_contains(expr, &|e| match e {
        Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::WeakFair(_, _)
        | Expr::StrongFair(_, _)
        | Expr::Enabled(_) => ScanDecision::Found,
        _ => ScanDecision::Continue,
    })
}

/// Check if an expression contains `ModuleRef` nodes (INSTANCE references).
///
/// Part of #2995: restored guard that prevents action-level Always terms containing
/// INSTANCE references from being promoted to BFS-inline implied actions. The compiled
/// guard Fallback evaluation path cannot correctly handle priming through INSTANCE WITH
/// substitutions in all cases — 3 specs (Peterson, EWD998ChanID, product) produce false
/// positives when this guard is absent.
///
/// Part of #2996: retained despite Steps 1-3 (SubstituteExpr fix, relowering, fold_state_var)
/// because the 3 target specs still fail without this guard. The underlying issue is deeper
/// than substitution — likely related to priming distribution through INSTANCE WITH in the
/// compiled guard evaluation path.
pub(crate) fn contains_module_ref(expr: &Expr) -> bool {
    expr_contains(expr, &|e| match e {
        Expr::ModuleRef(..) => ScanDecision::Found,
        _ => ScanDecision::Continue,
    })
}

/// Result of checking invariants for a successor state.
///
/// Shared by sequential (`check/model_checker`) and parallel (`parallel/worker`)
/// checker paths to prevent enum-shape drift.
///
/// Part of #2356 (Phase 1): unifies previously duplicated `InvariantOutcome`
/// definitions in `run_helpers.rs` and `parallel/worker.rs`.
#[derive(Debug)]
pub(crate) enum InvariantOutcome {
    /// Successor passed all invariants.
    Ok,
    /// Violation was recorded and exploration should continue.
    ViolationContinued,
    /// Invariant violated and checker should stop (unless caller converts to continue-on-error).
    Violation {
        invariant: String,
        state_fp: Fingerprint,
    },
    /// Fatal error during invariant evaluation.
    Error(CheckError),
}

/// Build a consistent depth-overflow error message for TLC level conversion.
pub(crate) fn depth_overflow_error(depth: usize) -> CheckError {
    ConfigCheckError::Setup(format!(
        "BFS depth {} exceeds TLC level range (max depth {})",
        depth,
        (u32::MAX - 1) as usize
    ))
    .into()
}

/// Convert a zero-based BFS depth to TLC's one-based `level` while handling overflow.
///
/// TLC uses 1-based levels: depth 0 -> level 1, depth 1 -> level 2, etc.
/// Returns `Err(ConfigCheckError::Setup)` if the depth exceeds `u32::MAX - 1`.
///
/// Both the sequential and parallel checkers MUST use this function for all
/// depth-to-level conversions. Raw `(depth + 1) as u32` casts are forbidden
/// because they silently truncate on 64-bit platforms.
pub(crate) fn depth_to_tlc_level(depth: usize) -> Result<u32, CheckError> {
    let one_based_depth = depth
        .checked_add(1)
        .ok_or_else(|| depth_overflow_error(depth))?;
    u32::try_from(one_based_depth).map_err(|_| depth_overflow_error(depth))
}

/// Build the final BFS runtime stats snapshot exposed to `TLCGet("stats")`.
///
/// TLC serves `TLCGet("stats")` from the checker's final counters during
/// POSTCONDITION evaluation, not from the last in-flight state exploration
/// snapshot. Queue and trace counts are always zero after BFS completion.
pub(crate) fn final_bfs_runtime_stats(stats: &CheckStats) -> Result<TlcRuntimeStats, CheckError> {
    let diameter = i64::from(depth_to_tlc_level(stats.max_depth)?);
    Ok(TlcRuntimeStats::new(
        stats.states_generated() as i64,
        stats.states_found as i64,
        0,
        0,
        diameter,
    ))
}

/// Check a fingerprint set for storage errors and return the canonical
/// `InfraCheckError::FingerprintOverflow` if any are present.
///
/// Returns `None` if no errors occurred. This centralizes the
/// `has_errors()` -> `CheckError` pattern used by both the sequential
/// `check_fingerprint_storage_errors()` and the parallel finalize path.
///
/// Part of #2056: eliminates the last duplication of `.max(1)` floor logic
/// between the two checker paths.
pub(crate) fn check_fingerprint_errors(seen_fps: &dyn FingerprintSet) -> Option<CheckError> {
    if seen_fps.has_errors() {
        Some(
            InfraCheckError::FingerprintOverflow {
                dropped: seen_fps.dropped_count().max(1),
                detail: String::from("post-BFS error flag detected on fingerprint set"),
            }
            .into(),
        )
    } else {
        None
    }
}

/// Convert a `StorageFault` into the canonical `InfraCheckError::FingerprintOverflow`.
///
/// The dropped count is floored to 1 because a storage fault always means at least
/// one insertion was lost, even if the counter hasn't been incremented yet.
///
/// Both the sequential and parallel checkers MUST use this function for all
/// `StorageFault` -> `CheckError` conversions. Inline construction of
/// `InfraCheckError::FingerprintOverflow` is forbidden to prevent drift in the
/// dropped-count floor logic.
///
/// Fix for #2481: passes through `StorageFault` detail for diagnostic context.
pub(crate) fn storage_fault_to_check_error(
    seen_fps: &dyn FingerprintSet,
    fault: &StorageFault,
) -> CheckError {
    InfraCheckError::FingerprintOverflow {
        dropped: seen_fps.dropped_count().max(1),
        detail: format!("{fault}"),
    }
    .into()
}

/// Atomically reserve one state-admission slot.
///
/// Uses a CAS loop to increment `admitted_count` only when it is below `limit`.
/// Returns `true` if a slot was reserved (counter incremented), `false` if the
/// limit has been reached.
///
/// Part of #2123: both checkers route state-admission decisions through this
/// function so the `max_states` contract cannot drift between serial and parallel.
pub(crate) fn try_reserve_state_slot(admitted_count: &AtomicUsize, limit: usize) -> bool {
    loop {
        let current = admitted_count.load(Ordering::Acquire);
        if current >= limit {
            return false;
        }
        if admitted_count
            .compare_exchange_weak(current, current + 1, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            return true;
        }
    }
}

/// Release a previously reserved state-admission slot.
///
/// Called when a reserved slot turns out to be a duplicate (dedup race) or
/// a storage fault occurs before the state is fully committed.
///
/// Part of #2123.
pub(crate) fn release_state_slot(admitted_count: &AtomicUsize) {
    admitted_count.fetch_sub(1, Ordering::Release);
}

// ---------------------------------------------------------------------------
// VIEW projection analysis and fast-path fingerprinting.
//
// When a VIEW is a simple variable projection (tuple or record of StateVars),
// we can compute its fingerprint directly from ArrayState slots, skipping
// the evaluator entirely. Complex VIEWs fall through to the eval path.
// ---------------------------------------------------------------------------

/// Describes the shape of a VIEW operator for fast-path fingerprinting.
///
/// Analyzed once per view_name per thread and cached in a thread-local.
/// Simple projections (tuple/record of state variables) enable direct
/// fingerprint computation from ArrayState slots, bypassing the evaluator.
#[derive(Debug, Clone)]
pub(crate) enum ViewProjection {
    /// VIEW is `<<var_i, var_j, ...>>` — tuple of state variables.
    /// Stores the VarIndex (u16) of each slot in tuple order.
    TupleSlots(Box<[u16]>),
    /// VIEW is `[f1 |-> var_i, f2 |-> var_j, ...]` — record of state variables.
    /// Stores (NameId, VarIndex) for each field.
    RecordSlots(Box<[(NameId, u16)]>),
    /// VIEW body is too complex for the fast path.
    Complex,
}

/// Analyze a VIEW operator's body to determine if it is a simple projection.
///
/// Returns `ViewProjection::TupleSlots` or `RecordSlots` when the VIEW body
/// is a tuple/record whose every element is a bare `StateVar`. Otherwise
/// returns `Complex`, which signals the caller to use the full evaluator.
pub(crate) fn analyze_view_projection(ctx: &EvalCtx, view_name: &str) -> ViewProjection {
    let Some(def) = ctx.get_op(view_name) else {
        return ViewProjection::Complex;
    };
    // Zero-parameter operators only (validated by prepare step).
    if !def.params.is_empty() {
        return ViewProjection::Complex;
    }
    let body = unwrap_label(&def.body.node);
    match body {
        Expr::Tuple(elems) => {
            let mut slots = Vec::with_capacity(elems.len());
            for elem in elems {
                let inner = unwrap_label(&elem.node);
                match inner {
                    Expr::StateVar(_name, idx, _name_id) => {
                        slots.push(*idx);
                    }
                    _ => return ViewProjection::Complex,
                }
            }
            ViewProjection::TupleSlots(slots.into_boxed_slice())
        }
        Expr::Record(fields) => {
            let mut record_slots = Vec::with_capacity(fields.len());
            for (field_name, field_expr) in fields {
                let inner = unwrap_label(&field_expr.node);
                match inner {
                    Expr::StateVar(_name, idx, _name_id) => {
                        let field_id = tla_core::intern_name(&field_name.node);
                        record_slots.push((field_id, *idx));
                    }
                    _ => return ViewProjection::Complex,
                }
            }
            ViewProjection::RecordSlots(record_slots.into_boxed_slice())
        }
        _ => ViewProjection::Complex,
    }
}

/// Unwrap nested `Label` wrappers (e.g., `P0:: expr`) to reach the inner expression.
fn unwrap_label(expr: &Expr) -> &Expr {
    match expr {
        Expr::Label(label) => unwrap_label(&label.body.node),
        other => other,
    }
}

/// Compute a VIEW fingerprint directly from ArrayState slots for simple projections.
///
/// Returns `Some(fp)` for tuple/record projections, `None` for complex VIEWs.
/// The fingerprint is computed using the same additive algorithm as
/// `compute_tuple_additive_fp` / `compute_record_additive_fp`, ensuring that
/// the fast path produces the same equivalence classes as the eval path.
pub(crate) fn compute_view_fingerprint_from_projection(
    array_state: &crate::state::ArrayState,
    projection: &ViewProjection,
) -> Option<Fingerprint> {
    use crate::state::{additive_entry_hash, compact_value_fingerprint, splitmix64, ADDITIVE_FUNC_SEED};
    use crate::var_index::VarIndex;

    match projection {
        ViewProjection::TupleSlots(slots) => {
            let mut fp = ADDITIVE_FUNC_SEED;
            fp = fp.wrapping_add(splitmix64(slots.len() as u64));
            for (i, &slot_idx) in slots.iter().enumerate() {
                let key_int = (i as i64) + 1; // 1-indexed, matching compute_tuple_additive_fp
                let key_fp = value_fingerprint(&crate::Value::SmallInt(key_int));
                let val_fp = compact_value_fingerprint(
                    array_state.get_compact(VarIndex(slot_idx)),
                );
                fp = fp.wrapping_add(additive_entry_hash(key_fp, val_fp));
            }
            Some(Fingerprint(fp))
        }
        ViewProjection::RecordSlots(fields) => {
            let mut fp = ADDITIVE_FUNC_SEED;
            fp = fp.wrapping_add(splitmix64(fields.len() as u64));
            for &(field_id, slot_idx) in fields.iter() {
                let key_fp = tla_core::resolve_name_id_string_fp64(field_id);
                let val_fp = compact_value_fingerprint(
                    array_state.get_compact(VarIndex(slot_idx)),
                );
                fp = fp.wrapping_add(additive_entry_hash(key_fp, val_fp));
            }
            Some(Fingerprint(fp))
        }
        ViewProjection::Complex => None,
    }
}

// ---------------------------------------------------------------------------
// Part of #2756: Canonical VIEW fingerprint computation shared between
// sequential and parallel checker paths. Previously each path had its own
// implementation with divergent tlc_level management.
// ---------------------------------------------------------------------------

/// Compute the fingerprint of a state with VIEW transformation applied.
///
/// This is the canonical VIEW fingerprint implementation used by both the
/// sequential checker (`ModelChecker::state_fingerprint`) and the parallel
/// checker (`parallel::worker::helpers::compute_view_fingerprint`). Both paths
/// MUST delegate to this function for VIEW fingerprinting to prevent parity
/// drift.
///
/// Evaluates the VIEW operator with the state variables bound to the context,
/// then fingerprints the result. This enables state abstraction where multiple
/// concrete states map to the same abstract fingerprint.
///
/// # tlc_level management
///
/// Self-contained: saves the current `tlc_level`, sets it to `bfs_level` for
/// the duration of the VIEW evaluation (so `TLCGet("level")` works in VIEW
/// expressions like `<<vars, TLCGet("level")>>`), then restores the previous
/// value. The `ScopeGuard` covers variable bindings but not `tlc_level`, so
/// the restore is manual.
///
/// # Arguments
/// * `ctx` - Evaluation context (must have VIEW operator loaded)
/// * `state` - State to fingerprint (variables will be bound to ctx)
/// * `view_name` - Name of the VIEW operator to evaluate
/// * `bfs_level` - BFS depth level for `TLCGet("level")` in VIEW expressions
pub(crate) fn compute_view_fingerprint(
    ctx: &mut EvalCtx,
    state: &State,
    view_name: &str,
    bfs_level: u32,
) -> Result<Fingerprint, CheckError> {
    // RAII guard restores env on drop (Part of #2738)
    let _scope_guard = ctx.scope_guard();
    let saved_level = ctx.get_tlc_level();

    // Set TLCGet("level") so VIEW expressions like <<vars, TLCGet("level")>> work correctly.
    // Without this, TLCGet("level") returns 0, collapsing states that differ only by BFS depth.
    ctx.set_tlc_level(bfs_level);

    // Bind state variables to the environment.
    for (name, value) in state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // Part of #3458/#3465: Clear eval-scope caches before VIEW evaluation.
    // Pair with identity invalidation to prevent LAST_STATE_PTR address reuse.
    crate::eval::clear_for_eval_scope_boundary();
    crate::eval::invalidate_state_identity_tracking();
    // Evaluate the VIEW operator.
    let result = ctx.eval_op(view_name);

    // Restore tlc_level manually (not covered by ScopeGuard).
    ctx.set_tlc_level(saved_level);

    // Part of #1424: propagate VIEW eval errors (TLC treats these as fatal).
    match result {
        Ok(value) => Ok(Fingerprint(value_fingerprint(&value))),
        Err(e) => Err(RuntimeCheckError::ViewEvalError {
            view_name: view_name.to_string(),
            eval_error: e,
        }
        .into()),
    }
}

/// Compute VIEW fingerprint from ArrayState (avoids State/OrdMap construction).
///
/// Part of #3022: ArrayState variant eliminates O(n) State conversion on the
/// parallel full-state successor path. Uses `bind_state_array_guard` for O(1)
/// array-based binding instead of iterating OrdMap entries.
///
/// Fast path: When the VIEW is a simple variable projection (tuple or record
/// of StateVars), the fingerprint is computed directly from ArrayState slots
/// using the additive fingerprint algorithm, skipping eval entirely. The
/// projection analysis is cached per view_name per thread.
pub(crate) fn compute_view_fingerprint_array(
    ctx: &mut EvalCtx,
    array_state: &crate::state::ArrayState,
    view_name: &str,
    bfs_level: u32,
) -> Result<Fingerprint, CheckError> {
    // Thread-local cache for the VIEW projection analysis.
    // Analyzed once per view_name per thread; simple projections bypass eval.
    thread_local! {
        static CACHED_PROJECTION: std::cell::RefCell<Option<(String, ViewProjection)>> =
            const { std::cell::RefCell::new(None) };
    }

    let fast_result = CACHED_PROJECTION.with(|cell| {
        let mut cache = cell.borrow_mut();
        if cache.as_ref().map_or(true, |(name, _)| name != view_name) {
            let projection = analyze_view_projection(ctx, view_name);
            *cache = Some((view_name.to_string(), projection));
        }
        let (_, ref projection) = *cache.as_ref().expect("just populated");
        compute_view_fingerprint_from_projection(array_state, projection)
    });

    if let Some(fp) = fast_result {
        return Ok(fp);
    }

    // Complex VIEW: fall through to the full evaluator path.
    let _scope_guard = ctx.scope_guard();
    let saved_level = ctx.get_tlc_level();
    ctx.set_tlc_level(bfs_level);

    let _state_guard = ctx.bind_state_env_guard(array_state.env_ref());
    // Part of #3458/#3465: Establish array-bound eval boundary before VIEW evaluation.
    crate::eval::clear_for_bound_state_eval_scope(ctx);

    let result = ctx.eval_op(view_name);
    ctx.set_tlc_level(saved_level);

    match result {
        Ok(value) => Ok(Fingerprint(value_fingerprint(&value))),
        Err(e) => Err(RuntimeCheckError::ViewEvalError {
            view_name: view_name.to_string(),
            eval_error: e,
        }
        .into()),
    }
}

#[cfg(test)]
#[path = "../checker_ops_tests/mod.rs"]
mod tests;

#[cfg(test)]
#[path = "../checker_ops_constraint_tests.rs"]
mod constraint_tests;
