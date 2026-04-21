// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, DiffSuccessor, UndoEntry};
use crate::var_index::VarRegistry;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Spanned, VarIndex};

#[cfg(debug_assertions)]
use super::emit_debug_line;
use super::{unified, DiffSink};

pub(super) fn run_unified(
    ctx: &mut EvalCtx,
    body: &Spanned<Expr>,
    current_array: &ArrayState,
    vars: &[Arc<str>],
    registry: &VarRegistry,
) -> Result<Vec<DiffSuccessor>, EvalError> {
    run_unified_with_tir(ctx, body, current_array, vars, registry, None)
}

/// Run unified successor enumeration with an optional TIR leaf evaluator.
///
/// Part of #3194: when `tir_leaf` is `Some`, leaf `eval` calls inside the
/// enumerator try TIR lowering + evaluation first.
pub(super) fn run_unified_with_tir<'a>(
    ctx: &mut EvalCtx,
    body: &Spanned<Expr>,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    registry: &'a VarRegistry,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<Vec<DiffSuccessor>, EvalError> {
    run_unified_with_options(ctx, body, current_array, vars, registry, tir_leaf, None)
}

/// Run unified successor enumeration with TIR leaf and pc-guard hoisting.
///
/// Part of #3923: when `pc_var_idx` is `Some`, Or branches with non-matching
/// `pc = "label"` guards are skipped, avoiding wasted evaluation in PlusCal specs.
pub(super) fn run_unified_with_options<'a>(
    ctx: &mut EvalCtx,
    body: &Spanned<Expr>,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    registry: &'a VarRegistry,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
    pc_var_idx: Option<VarIndex>,
) -> Result<Vec<DiffSuccessor>, EvalError> {
    let owned_base;
    let base_ref: &ArrayState = if current_array.has_complete_fp_cache() {
        current_array
    } else {
        owned_base = {
            let mut b = current_array.clone();
            b.ensure_fp_cache_with_value_fps(registry);
            b
        };
        &owned_base
    };

    let mut working = current_array.clone_for_working();
    let mut undo_stack: Vec<UndoEntry> = Vec::with_capacity(vars.len() * 2);
    let mut diffs = Vec::with_capacity(8);

    let mut params = unified::EnumParams::new(vars, registry, base_ref).with_tir_leaf(tir_leaf);
    if let Some(idx) = pc_var_idx {
        params = params.with_pc_guard_hoist(idx);
    }
    let mut rec = unified::RecState {
        working: &mut working,
        undo: &mut undo_stack,
        results: &mut diffs,
    };
    match unified::enumerate_unified(ctx, body, &params, &mut rec) {
        Ok(()) => {
            #[cfg(debug_assertions)]
            {
                use std::sync::atomic::{AtomicU64, Ordering};
                static STATE_COUNT: AtomicU64 = AtomicU64::new(0);
                static MULTI_COUNT: AtomicU64 = AtomicU64::new(0);
                static TOTAL_SUCCS: AtomicU64 = AtomicU64::new(0);
                let state_num = STATE_COUNT.fetch_add(1, Ordering::Relaxed);
                TOTAL_SUCCS.fetch_add(diffs.len() as u64, Ordering::Relaxed);
                if crate::check::debug::debug_state_succs() && diffs.len() > 1 {
                    let multi = MULTI_COUNT.fetch_add(1, Ordering::Relaxed);
                    if multi < 50 {
                        emit_debug_line(
                            true,
                            format_args!(
                                "[run_unified] state={} successors={} (multi #{})",
                                state_num,
                                diffs.len(),
                                multi
                            ),
                        );
                    }
                }
                if crate::check::debug::debug_dump_succs() && state_num < 5 {
                    emit_debug_line(
                        true,
                        format_args!("=== State {} ({} successors) ===", state_num, diffs.len()),
                    );
                    emit_debug_line(
                        true,
                        format_args!(
                            "  Base: {:?}",
                            current_array
                                .materialize_values()
                                .iter()
                                .enumerate()
                                .map(|(i, v)| format!("{}={}", vars[i], v))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    );
                    for (si, diff) in diffs.iter().enumerate() {
                        let succ = diff.materialize(base_ref, registry);
                        emit_debug_line(
                            true,
                            format_args!(
                                "  Succ {}: {:?}",
                                si,
                                succ.materialize_values()
                                    .iter()
                                    .enumerate()
                                    .map(|(i, v)| format!("{}={}", vars[i], v))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                        );
                    }
                }
            }
            Ok(diffs)
        }
        Err(e) => Err(e),
    }
}

/// Run unified successor enumeration into a DiffSink with an optional TIR leaf.
///
/// Part of #3294: when `tir_leaf` is `Some`, leaf `eval` calls inside the
/// enumerator try TIR lowering + evaluation first, enabling TIR eval on
/// the streaming successor path.
pub(super) fn run_unified_into<'a>(
    ctx: &mut EvalCtx,
    body: &Spanned<Expr>,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    registry: &'a VarRegistry,
    sink: &mut dyn DiffSink,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<(), EvalError> {
    run_unified_into_with_options(ctx, body, current_array, vars, registry, sink, tir_leaf, None)
}

/// Run unified successor enumeration into a DiffSink with TIR leaf and pc-guard hoisting.
///
/// Part of #3923: when `pc_var_idx` is `Some`, Or branches with non-matching
/// `pc = "label"` guards are skipped during enumeration.
pub(super) fn run_unified_into_with_options<'a>(
    ctx: &mut EvalCtx,
    body: &Spanned<Expr>,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    registry: &'a VarRegistry,
    sink: &mut dyn DiffSink,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
    pc_var_idx: Option<VarIndex>,
) -> Result<(), EvalError> {
    let owned_base;
    let base_ref: &ArrayState = if current_array.has_complete_fp_cache() {
        current_array
    } else {
        owned_base = {
            let mut b = current_array.clone();
            b.ensure_fp_cache_with_value_fps(registry);
            b
        };
        &owned_base
    };

    let mut working = current_array.clone_for_working();
    let mut undo_stack: Vec<UndoEntry> = Vec::with_capacity(vars.len() * 2);

    let mut params = unified::EnumParams::new(vars, registry, base_ref).with_tir_leaf(tir_leaf);
    if let Some(idx) = pc_var_idx {
        params = params.with_pc_guard_hoist(idx);
    }
    let mut rec = unified::RecState {
        working: &mut working,
        undo: &mut undo_stack,
        results: sink,
    };
    unified::enumerate_unified(ctx, body, &params, &mut rec)
}

/// Test helpers for exercising `run_unified_with_options` with pc-guard hoisting.
#[cfg(test)]
pub(crate) mod successor_engine_test_helpers {
    use super::*;

    /// Run unified successor enumeration with pc-guard hoisting enabled.
    ///
    /// Returns DiffSuccessors (not ArrayStates) for comparison with the
    /// non-hoisted path. Part of #3923 guard hoisting tests.
    pub(crate) fn run_with_pc_hoist<'a>(
        ctx: &mut crate::eval::EvalCtx,
        body: &tla_core::Spanned<tla_core::ast::Expr>,
        current_array: &crate::state::ArrayState,
        vars: &'a [std::sync::Arc<str>],
        registry: &'a crate::var_index::VarRegistry,
        pc_var_idx: VarIndex,
    ) -> Result<Vec<crate::state::DiffSuccessor>, crate::error::EvalError> {
        run_unified_with_options(ctx, body, current_array, vars, registry, None, Some(pc_var_idx))
    }
}
