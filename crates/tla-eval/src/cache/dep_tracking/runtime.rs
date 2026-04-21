// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime state and read-recording helpers for dependency tracking.
//!
//! Contains `EvalRuntimeState`, `OpDepFrame`, `StateLookupMode`, and the
//! `record_*` / `mark_*` / `propagate_*` functions that modify the dep stack
//! during evaluation.

use super::deps::OpEvalDeps;
use crate::core::TlcRuntimeStats;
use crate::value::Value;
use crate::var_index::VarIndex;
use crate::EvalCtx;
use tla_core::name_intern::NameId;

pub(crate) struct OpDepFrame {
    pub(crate) deps: OpEvalDeps,
    /// Stack depth at the start of this operator evaluation.
    /// Variables at indices >= this are internal iteration variables and should
    /// NOT be recorded as dependencies (they don't affect caching validity).
    pub(crate) base_stack_len: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StateLookupMode {
    Current,
    Next,
}

pub(crate) struct EvalRuntimeState {
    pub(crate) stacker_counter: std::cell::Cell<u8>,
    pub(crate) op_dep_stack: std::cell::RefCell<Vec<OpDepFrame>>,
    /// Part of #3666: Shadow counter for `op_dep_stack.len()` to avoid RefCell
    /// borrows on the hot path. Incremented by `OpDepGuard::new`, decremented
    /// by `OpDepGuard::drop`/`try_take_deps`.
    pub(crate) dep_tracking_depth: std::cell::Cell<u16>,
    pub(crate) state_lookup_mode: std::cell::Cell<StateLookupMode>,
    pub(crate) input_base_dir: std::cell::RefCell<Option<std::path::PathBuf>>,
    pub(crate) tlc_runtime_stats: std::cell::RefCell<Option<TlcRuntimeStats>>,
    pub(crate) simulation_rng_state: std::cell::RefCell<Option<u64>>,
    /// Shadow of the `HOIST_ACTIVE` thread-local for O(1) check without TLS
    /// lookup on the eval_expr hot path. Set/cleared by quantifier eval
    /// functions that have ctx access, mirroring the thread-local flag.
    /// 413M+ eval calls/run × ~2-3ns TLS lookup = ~1s saved.
    pub(crate) hoist_active: std::cell::Cell<bool>,
    /// Part of #3962: Shadow of LAST_STATE_GEN thread-local. Eliminates 1 TLS
    /// lookup per enter_eval_boundary call. Updated in enter_eval_boundary
    /// when state_changed is detected.
    pub(crate) last_state_gen: std::cell::Cell<u64>,
    /// Part of #3962: Shadow of LAST_NEXT_STATE_GEN thread-local. Eliminates
    /// 1 TLS lookup per enter_eval_boundary call.
    pub(crate) last_next_state_gen: std::cell::Cell<u64>,
    /// Part of #3962: Shadow of LAST_STATE_PTR thread-local. Eliminates 1 TLS
    /// lookup per enter_eval_boundary call when state changes.
    pub(crate) last_state_ptr: std::cell::Cell<usize>,
    /// Part of #3962: Shadow of LAST_NEXT_STATE_PTR thread-local. Eliminates
    /// 1 TLS lookup per enter_eval_boundary call when state changes.
    pub(crate) last_next_state_ptr: std::cell::Cell<usize>,
    /// Part of #3962: Shadow of EVAL_EXIT_COUNT thread-local. Eliminates 1 TLS
    /// lookup per eval_entry exit.
    pub(crate) eval_exit_count: std::cell::Cell<u32>,
    /// Part of #3962: Shadow of IN_ENABLED_SCOPE thread-local. Eliminates 1 TLS
    /// lookup per cache insertion point check. Synced every 64 evals in eval()
    /// alongside hoist_active.
    pub(crate) in_enabled_scope: std::cell::Cell<bool>,
    /// Part of #3962: Shadow of STATE_GENERATION thread-local. Eliminates 1 TLS
    /// read per enter_eval_boundary call. Writers (advance_state_generation) update
    /// both TLS and shadow; readers (enter_eval_boundary) read shadow only.
    pub(crate) state_generation: std::cell::Cell<u64>,
    /// Part of #3962: Shadow of NEXT_STATE_GENERATION thread-local. Eliminates
    /// 1 TLS read per enter_eval_boundary call.
    pub(crate) next_state_generation: std::cell::Cell<u64>,
    /// Part of #3962: Shadow of HOIST_STATE_GENERATION thread-local. Eliminates
    /// 2 TLS reads per eval_expr call (1 in quantifier_hoist_lookup, 1 in
    /// quantifier_hoist_store). Synced every 64 evals alongside hoist_active.
    /// Updated at hoist scope entry/exit and generation bump boundaries.
    pub(crate) hoist_state_generation: std::cell::Cell<u32>,
}

impl EvalRuntimeState {
    pub(crate) fn new() -> Self {
        Self {
            stacker_counter: std::cell::Cell::new(0),
            op_dep_stack: std::cell::RefCell::new(Vec::new()),
            dep_tracking_depth: std::cell::Cell::new(0),
            state_lookup_mode: std::cell::Cell::new(StateLookupMode::Current),
            input_base_dir: std::cell::RefCell::new(None),
            tlc_runtime_stats: std::cell::RefCell::new(None),
            simulation_rng_state: std::cell::RefCell::new(None),
            hoist_active: std::cell::Cell::new(false),
            last_state_gen: std::cell::Cell::new(0),
            last_next_state_gen: std::cell::Cell::new(0),
            last_state_ptr: std::cell::Cell::new(0),
            last_next_state_ptr: std::cell::Cell::new(0),
            eval_exit_count: std::cell::Cell::new(0),
            in_enabled_scope: std::cell::Cell::new(false),
            state_generation: std::cell::Cell::new(0),
            next_state_generation: std::cell::Cell::new(0),
            hoist_state_generation: std::cell::Cell::new(0),
        }
    }
}

pub(crate) fn current_state_lookup_mode(ctx: &EvalCtx) -> StateLookupMode {
    ctx.runtime_state.state_lookup_mode.get()
}

pub(crate) fn record_local_read(
    ctx: &EvalCtx,
    resolved_stack_index: usize,
    name_id: NameId,
    value: &Value,
) {
    // Part of #3666: fast check avoids RefCell borrow when dep tracking is inactive.
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    // Issue #70 fix + #113 refinement: Record outer-scope variables as dependencies,
    // but NOT internal iteration variables.
    //
    // The key insight: variables pushed AFTER the operator evaluation started
    // (resolved_stack_index >= base_stack_len) are internal iteration variables
    // from comprehensions like `{ ... : n \in S }`. These should NOT be recorded
    // because they don't affect the result's validity for caching purposes.
    //
    // Variables pushed BEFORE the operator started (resolved_stack_index < base_stack_len)
    // are from outer scopes and SHOULD be recorded as dependencies.
    //
    // This fixes the performance issue in SpanTreeRandom where the `Edges` operator
    // uses comprehensions and was incorrectly marking deps as inconsistent.
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    // Only record if this variable was on the stack BEFORE the operator started
    if resolved_stack_index < top.base_stack_len {
        top.deps.record_local(name_id, value);
    }
    // Variables at indices >= base_stack_len are internal iteration variables
    // and should not affect cache validity
}

pub(crate) fn record_state_read(ctx: &EvalCtx, idx: VarIndex, value: &Value) {
    // Part of #3666: fast check avoids RefCell borrow_mut when dep tracking is inactive.
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    match current_state_lookup_mode(ctx) {
        StateLookupMode::Current => top.deps.record_state(idx, value),
        StateLookupMode::Next => top.deps.record_next(idx, value),
    }
}

/// Fix #3062: Record that TLCGet("level") was read during operator evaluation.
/// Without this, zero-arg operators that call TLCGet("level") get cached with
/// empty deps and are never invalidated across BFS levels.
pub(crate) fn record_tlc_level_read(ctx: &EvalCtx) {
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    top.deps.record_tlc_level(ctx.tlc_level);
}

/// Mark the current operator evaluation as runtime-volatile and thus non-cacheable.
///
/// Used for simulation-only randomness and time-dependent TLCGet values that are
/// not functions of the current state or BFS level.
pub(crate) fn mark_runtime_nondeterministic(ctx: &EvalCtx) {
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    top.deps.inconsistent = true;
}

/// Fix #3447: Mark the current dep-tracking frame as having touched an INSTANCE
/// LazyBinding. This prevents the enclosing operator's result from being stored
/// in the persistent cache partition even when concrete dep sets are empty.
pub(crate) fn mark_instance_lazy_read(ctx: &EvalCtx) {
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    top.deps.instance_lazy_read = true;
}

pub(crate) fn record_next_read(ctx: &EvalCtx, idx: VarIndex, value: &Value) {
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    top.deps.record_next(idx, value);
}

pub(crate) fn propagate_cached_deps(ctx: &EvalCtx, deps: &OpEvalDeps) {
    if ctx.runtime_state.dep_tracking_depth.get() == 0 {
        return;
    }
    let mut stack = ctx.runtime_state.op_dep_stack.borrow_mut();
    let Some(top) = stack.last_mut() else {
        return;
    };
    top.deps.merge_from(deps);
}

/// Check if dep tracking is currently active (op_dep_stack is non-empty).
///
/// Part of #3666: Uses the `dep_tracking_depth` Cell counter instead of
/// borrowing the RefCell, eliminating borrow flag management overhead on
/// the eval_tir_expr hot path.
#[inline]
pub(crate) fn is_dep_tracking_active(ctx: &EvalCtx) -> bool {
    ctx.runtime_state.dep_tracking_depth.get() > 0
}
