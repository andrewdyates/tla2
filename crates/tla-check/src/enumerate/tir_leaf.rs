// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR leaf evaluation helpers.
//!
//! Part of #3194: replaces leaf `eval(ctx, expr)` calls with TIR evaluation
//! where the bootstrap lowerer supports the expression. Falls back to AST
//! `eval` when TIR lowering fails.
//!
//! Two variants:
//! - [`eval_leaf`]: uses `eval()` directly (for enumerate hot paths where the
//!   caller manages cache lifecycle)
//! - [`eval_leaf_entry`]: uses `eval_entry()` with cache lifecycle management
//!   (for liveness and other top-level eval sites)

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use tla_core::ast::Expr;
use tla_core::{pretty_expr, Spanned};

use crate::eval::{eval, eval_entry, EvalCtx};
use tla_eval::tir::{TirExprEvalAttempt, TirProgram};
use tla_value::error::EvalResult;
use tla_value::Value;

feature_flag!(tir_leaf_parity_enabled, "TLA2_TIR_LEAF_PARITY");
feature_limit!(
    tir_leaf_parity_log_limit,
    "TLA2_TIR_LEAF_PARITY_LOG_LIMIT",
    20
);

const TIR_LEAF_PARITY_EXPR_LIMIT: usize = 240;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct TirLeafParityCounts {
    comparisons: usize,
    mismatches: usize,
}

static TIR_LEAF_PARITY_STATS: OnceLock<Mutex<BTreeMap<String, TirLeafParityCounts>>> =
    OnceLock::new();
static TIR_LEAF_PARITY_LOGGED: AtomicUsize = AtomicUsize::new(0);

fn tir_leaf_parity_stats() -> &'static Mutex<BTreeMap<String, TirLeafParityCounts>> {
    TIR_LEAF_PARITY_STATS.get_or_init(|| Mutex::new(BTreeMap::new()))
}

#[cfg(test)]
fn clear_tir_leaf_parity_stats_for_test() {
    if let Some(stats) = TIR_LEAF_PARITY_STATS.get() {
        stats
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clear();
    }
    TIR_LEAF_PARITY_LOGGED.store(0, Ordering::Relaxed);
}

#[cfg(test)]
fn tir_leaf_parity_snapshot_for_test() -> BTreeMap<String, TirLeafParityCounts> {
    tir_leaf_parity_stats()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone()
}

fn eval_leaf_impl(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    tir: Option<&TirProgram<'_>>,
    ast_eval: fn(&EvalCtx, &Spanned<Expr>) -> EvalResult<Value>,
    parity_enabled: bool,
) -> EvalResult<Value> {
    let Some(tir) = tir else {
        return ast_eval(ctx, expr);
    };

    if !parity_enabled {
        if let Some(result) = tir.try_eval_expr(ctx, expr) {
            // Part of #3460: TIR eval internally calls eval_named_op, eval_op,
            // and other AST-side functions that set LAST_STATE_PTR / LAST_NEXT_STATE_PTR
            // and populate per-state caches. Even when TIR succeeds, these side effects
            // contaminate subsequent leaf evaluations in the same successor step.
            // Invalidate both state and next-state identity tracking so the next
            // eval_entry() call forces a full cache boundary dispatch instead of
            // reusing stale identity pointers.
            crate::eval::invalidate_state_identity_tracking();
            crate::eval::invalidate_next_state_identity_tracking();
            return result;
        }
        // Part of #3460: When try_eval_expr returns None because TIR evaluation
        // produced an error (Evaluated(Err)), eval_tir already ran and polluted
        // caches (state-identity tracking, eager bindings, operator caches).
        // The subsequent AST fallback sees this stale state. Invalidate both
        // identity trackers so the next eval_entry() forces a fresh cache boundary.
        crate::eval::invalidate_state_identity_tracking();
        crate::eval::invalidate_next_state_identity_tracking();
        return ast_eval(ctx, expr);
    }

    // Evaluate the AST baseline first so parity compares against an
    // uncontaminated result even if the TIR path mutates shared runtime state.
    let ast_result = ast_eval(ctx, expr);
    match tir.try_eval_expr_detailed(ctx, expr) {
        TirExprEvalAttempt::Unsupported => ast_result,
        TirExprEvalAttempt::Evaluated(tir_result) => {
            let label = tir_leaf_label(tir);
            record_tir_leaf_parity(&label, expr, &ast_result, &tir_result);
            if tir_result.is_ok() {
                tir_result
            } else {
                ast_result
            }
        }
    }
}

fn tir_leaf_label(tir: &TirProgram<'_>) -> String {
    let labels = tir.probe_labels();
    if labels.is_empty() {
        "<unlabeled>".to_string()
    } else {
        labels.join("|")
    }
}

fn record_tir_leaf_parity(
    label: &str,
    expr: &Spanned<Expr>,
    ast_result: &EvalResult<Value>,
    tir_result: &EvalResult<Value>,
) {
    let mismatch = !eval_results_match(ast_result, tir_result);
    {
        let mut stats = tir_leaf_parity_stats()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let entry = stats.entry(label.to_string()).or_default();
        entry.comparisons += 1;
        if mismatch {
            entry.mismatches += 1;
        }
    }

    if !mismatch {
        return;
    }

    let idx = TIR_LEAF_PARITY_LOGGED.fetch_add(1, Ordering::Relaxed);
    let limit = tir_leaf_parity_log_limit();
    if idx < limit {
        eprintln!(
            "TLA2_TIR_LEAF_PARITY mismatch[{}/{}] op={} span={:?} expr={} AST={} TIR={}",
            idx + 1,
            limit,
            label,
            expr.span,
            summarize_expr(expr),
            format_eval_result(ast_result),
            format_eval_result(tir_result)
        );
    } else if idx == limit {
        eprintln!(
            "TLA2_TIR_LEAF_PARITY additional mismatches suppressed after {} lines; \
set TLA2_TIR_LEAF_PARITY_LOG_LIMIT to raise the cap",
            limit
        );
    }
}

fn summarize_expr(expr: &Spanned<Expr>) -> String {
    let mut text = pretty_expr(&expr.node).replace('\n', " ");
    if text.len() > TIR_LEAF_PARITY_EXPR_LIMIT {
        text.truncate(TIR_LEAF_PARITY_EXPR_LIMIT);
        text.push_str("...");
    }
    text
}

fn eval_results_match(left: &EvalResult<Value>, right: &EvalResult<Value>) -> bool {
    match (left, right) {
        (Ok(left), Ok(right)) => left == right,
        (Err(left), Err(right)) => format!("{left:?}") == format!("{right:?}"),
        _ => false,
    }
}

fn format_eval_result(result: &EvalResult<Value>) -> String {
    match result {
        Ok(value) => format!("Ok({value:?})"),
        Err(error) => format!("Err({error:?})"),
    }
}

/// Evaluate a leaf expression, trying TIR first if a TIR evaluator is active.
///
/// When `tir` is `Some`, attempts TIR lowering + evaluation first. If TIR
/// lowering is unsupported for this expression, falls back to AST `eval`.
/// When `tir` is `None`, uses AST `eval` unconditionally.
///
/// This is the dual-system seam: the enumerator calls `eval_leaf` at every
/// value-level leaf site, and the caller controls whether TIR is active via
/// the `EnumParams.tir_leaf` field.
#[inline]
pub(super) fn eval_leaf(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    tir: Option<&TirProgram<'_>>,
) -> EvalResult<Value> {
    eval_leaf_impl(ctx, expr, tir, eval, tir_leaf_parity_enabled())
}

/// Evaluate a leaf expression with `eval_entry` cache lifecycle management.
///
/// Same TIR-first semantics as [`eval_leaf`], but falls back to `eval_entry`
/// instead of `eval`. Use this at top-level evaluation boundaries (liveness,
/// property checking) where the caller does not manage the SUBST_CACHE.
///
/// Part of #3194: liveness subsystem TIR wiring.
#[inline]
pub(crate) fn eval_leaf_entry(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    tir: Option<&TirProgram<'_>>,
) -> EvalResult<Value> {
    eval_leaf_impl(ctx, expr, tir, eval_entry, tir_leaf_parity_enabled())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::clear_for_test_reset;
    use crate::test_support::parse_module;
    use tla_core::ast::{Module, Unit};
    fn find_operator_body<'a>(module: &'a Module, name: &str) -> &'a Spanned<Expr> {
        module
            .units
            .iter()
            .find_map(|unit| match &unit.node {
                Unit::Operator(def) if def.name.node == name => Some(&def.body),
                _ => None,
            })
            .unwrap_or_else(|| panic!("operator '{name}' should exist"))
    }

    fn reset_leaf_parity_test_state() {
        clear_for_test_reset();
        // Part of #4067: Use reset_global_state() instead of direct
        // clear_global_name_interner() to respect the active-run guard.
        // Direct clearing corrupts the name interner for concurrent tests.
        crate::reset_global_state();
        clear_tir_leaf_parity_stats_for_test();
    }

    #[test]
    fn test_eval_leaf_parity_counts_matching_comparison() {
        reset_leaf_parity_test_state();
        let module = parse_module(
            "\
---- MODULE TirLeafParityMatch ----
Leaf == 1 + 1
====",
        );
        let expr = find_operator_body(&module, "Leaf");
        let program = TirProgram::from_modules(&module, &[]).with_probe_label("LeafMatch");
        let ctx = EvalCtx::new();

        let result =
            eval_leaf_impl(&ctx, expr, Some(&program), eval, true).expect("leaf eval should work");
        assert_eq!(
            result,
            Value::int(2),
            "parity mode must keep the TIR result"
        );

        let snapshot = tir_leaf_parity_snapshot_for_test();
        let counts = snapshot.get("LeafMatch").copied().unwrap_or_default();
        assert_eq!(counts.comparisons, 1, "parity mode should compare one leaf");
        assert_eq!(counts.mismatches, 0, "matching leaf should not be flagged");
    }

    #[test]
    fn test_record_tir_leaf_parity_tracks_mismatch() {
        reset_leaf_parity_test_state();
        let module = parse_module(
            "\
---- MODULE TirLeafParityMismatch ----
Leaf == 1 + 1
====",
        );
        let expr = find_operator_body(&module, "Leaf");

        record_tir_leaf_parity("LeafMismatch", expr, &Ok(Value::int(2)), &Ok(Value::int(3)));

        let snapshot = tir_leaf_parity_snapshot_for_test();
        let counts = snapshot.get("LeafMismatch").copied().unwrap_or_default();
        assert_eq!(
            counts.comparisons, 1,
            "mismatch should count as a comparison"
        );
        assert_eq!(counts.mismatches, 1, "mismatch should be recorded");
    }
}
