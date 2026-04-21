// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge between liveness `LiveExpr` leaves and the JIT-compiled liveness
//! predicate evaluator in `tla-jit`.
//!
//! This module:
//! 1. Extracts `LivenessPredInfo` descriptors from `LiveExpr` leaf nodes
//! 2. Compiles them via `tla_jit::compile_liveness_predicates`
//! 3. Provides integration functions for inline recording to use compiled
//!    predicates when available
//!
//! Part of #3992: JIT V2 Phase 10 — Compiled Liveness.

use crate::check::model_checker::ModelChecker;
use crate::liveness::LiveExpr;
use tla_core::ast::Expr;
use tla_jit::compiled_liveness::{LivenessPredInfo, LivenessPredKind, ScalarCompOp};
use tla_jit::compound_layout::StateLayout;

/// Extract `LivenessPredInfo` from a slice of fairness state/action leaves.
///
/// State predicates and action predicates are tagged with their respective
/// `is_state_pred` flag. `Enabled` and `StateChanged` leaves are marked
/// `NotEligible` since they require runtime evaluation (successor enumeration
/// or compound value comparison).
pub(super) fn extract_pred_infos(
    state_leaves: &[LiveExpr],
    action_leaves: &[LiveExpr],
) -> Vec<LivenessPredInfo> {
    let mut infos = Vec::with_capacity(state_leaves.len() + action_leaves.len());

    for leaf in state_leaves {
        infos.push(live_expr_to_pred_info(leaf, true));
    }
    for leaf in action_leaves {
        infos.push(live_expr_to_pred_info(leaf, false));
    }

    infos
}

/// Convert a single `LiveExpr` leaf to a `LivenessPredInfo`.
///
/// Part of #3992: Analyzes `StatePred` and `ActionPred` AST expressions to
/// detect simple scalar comparison patterns that can be compiled to native
/// code. When the expression is a direct comparison between state variables
/// and/or integer constants (e.g., `x = 5`, `x > y`), a compilable
/// `LivenessPredKind` is produced. Otherwise, falls back to `NotEligible`.
fn live_expr_to_pred_info(leaf: &LiveExpr, is_state_pred: bool) -> LivenessPredInfo {
    let tag = leaf.tag().unwrap_or(0);

    match leaf {
        LiveExpr::StatePred {
            tag,
            expr,
            bindings,
        } => {
            // Bound variables make compilation non-trivial -- fall back.
            if bindings.is_some() {
                return LivenessPredInfo {
                    tag: *tag,
                    is_state_pred,
                    var_indices: vec![],
                    kind: LivenessPredKind::NotEligible,
                };
            }
            let (kind, var_indices) = try_analyze_comparison_expr(&expr.node);
            LivenessPredInfo {
                tag: *tag,
                is_state_pred,
                var_indices,
                kind,
            }
        }

        LiveExpr::ActionPred {
            tag,
            expr,
            bindings,
        } => {
            if bindings.is_some() {
                return LivenessPredInfo {
                    tag: *tag,
                    is_state_pred,
                    var_indices: vec![],
                    kind: LivenessPredKind::NotEligible,
                };
            }
            let (kind, var_indices) = try_analyze_comparison_expr(&expr.node);
            LivenessPredInfo {
                tag: *tag,
                is_state_pred,
                var_indices,
                kind,
            }
        }

        // ENABLED requires successor enumeration -- never compilable to a
        // simple predicate function.
        LiveExpr::Enabled { tag, .. } => LivenessPredInfo {
            tag: *tag,
            is_state_pred: true, // ENABLED is always a state predicate
            var_indices: vec![],
            kind: LivenessPredKind::NotEligible,
        },

        // StateChanged: subscript-based uses interpreter. Null-subscript with no
        // bindings can be compiled as a StateChangeCheck on all variables.
        LiveExpr::StateChanged {
            tag,
            subscript,
            bindings,
            ..
        } => {
            if bindings.is_some() || subscript.is_some() {
                return LivenessPredInfo {
                    tag: *tag,
                    is_state_pred: false,
                    var_indices: vec![],
                    kind: LivenessPredKind::NotEligible,
                };
            }
            // Null subscript = "any variable changed". Compile as StateChangeCheck
            // on all variable indices. The compiled function will compare
            // current[i] != next[i] for each variable, returning true if any differ.
            // The caller must populate var_indices with the actual variable count
            // via `populate_state_change_var_indices` after layout is known.
            LivenessPredInfo {
                tag: *tag,
                is_state_pred: false,
                var_indices: vec![],
                kind: LivenessPredKind::StateChangeCheck {
                    var_indices: vec![], // placeholder; populated by caller
                },
            }
        }

        // Boolean constants and temporal operators should not appear as leaves.
        _ => LivenessPredInfo {
            tag,
            is_state_pred,
            var_indices: vec![],
            kind: LivenessPredKind::NotEligible,
        },
    }
}

/// Try to extract a scalar comparison pattern from a top-level comparison AST node.
///
/// Recognized patterns:
/// - `StateVar op Int` -> `ScalarComparison`
/// - `Int op StateVar` -> `ScalarComparison` (with flipped op)
/// - `StateVar op StateVar` -> `VarComparison`
///
/// Returns `(kind, var_indices)` where `var_indices` lists the state variable
/// indices referenced by the comparison (for documentation/debugging).
fn try_analyze_comparison_expr(expr: &Expr) -> (LivenessPredKind, Vec<u16>) {
    // Extract (lhs, rhs, op) from comparison AST nodes.
    let (lhs, rhs, op) = match expr {
        Expr::Eq(lhs, rhs) => (&lhs.node, &rhs.node, ScalarCompOp::Eq),
        Expr::Neq(lhs, rhs) => (&lhs.node, &rhs.node, ScalarCompOp::Ne),
        Expr::Lt(lhs, rhs) => (&lhs.node, &rhs.node, ScalarCompOp::Lt),
        Expr::Leq(lhs, rhs) => (&lhs.node, &rhs.node, ScalarCompOp::Le),
        Expr::Gt(lhs, rhs) => (&lhs.node, &rhs.node, ScalarCompOp::Gt),
        Expr::Geq(lhs, rhs) => (&lhs.node, &rhs.node, ScalarCompOp::Ge),
        _ => return (LivenessPredKind::NotEligible, vec![]),
    };

    // Pattern: StateVar op Int
    if let (Expr::StateVar(_, idx, _), Some(constant)) = (lhs, try_extract_i64(rhs)) {
        return (
            LivenessPredKind::ScalarComparison {
                var_idx: *idx,
                op,
                constant,
            },
            vec![*idx],
        );
    }

    // Pattern: Int op StateVar (flip the comparison)
    if let (Some(constant), Expr::StateVar(_, idx, _)) = (try_extract_i64(lhs), rhs) {
        return (
            LivenessPredKind::ScalarComparison {
                var_idx: *idx,
                op: flip_comparison_op(op),
                constant,
            },
            vec![*idx],
        );
    }

    // Pattern: StateVar op StateVar
    if let (Expr::StateVar(_, lhs_idx, _), Expr::StateVar(_, rhs_idx, _)) = (lhs, rhs) {
        return (
            LivenessPredKind::VarComparison {
                lhs_var_idx: *lhs_idx,
                rhs_var_idx: *rhs_idx,
                op,
            },
            vec![*lhs_idx, *rhs_idx],
        );
    }

    (LivenessPredKind::NotEligible, vec![])
}

/// Try to extract an i64 constant from an AST expression.
///
/// Returns `Some(value)` for `Expr::Int` when the BigInt fits in i64,
/// `None` otherwise.
fn try_extract_i64(expr: &Expr) -> Option<i64> {
    if let Expr::Int(big) = expr {
        i64::try_from(big).ok()
    } else {
        None
    }
}

/// Flip a comparison operator for when operands are swapped.
///
/// `5 < x` is equivalent to `x > 5`, so `Lt` becomes `Gt`, etc.
/// `Eq` and `Ne` are symmetric and unchanged.
fn flip_comparison_op(op: ScalarCompOp) -> ScalarCompOp {
    match op {
        ScalarCompOp::Eq => ScalarCompOp::Eq,
        ScalarCompOp::Ne => ScalarCompOp::Ne,
        ScalarCompOp::Lt => ScalarCompOp::Gt,
        ScalarCompOp::Le => ScalarCompOp::Ge,
        ScalarCompOp::Gt => ScalarCompOp::Lt,
        ScalarCompOp::Ge => ScalarCompOp::Le,
    }
}

/// Populate `StateChangeCheck` predicates with all variable indices from the layout.
///
/// During `live_expr_to_pred_info`, null-subscript `StateChanged` predicates are
/// created with empty `var_indices` because the layout is not yet known. This
/// function fills them in so the compiled code checks all variables for changes.
fn populate_state_change_var_indices(pred_infos: &mut [LivenessPredInfo], layout: &StateLayout) {
    let num_vars = layout.var_count();
    if num_vars == 0 {
        return;
    }
    let all_indices: Vec<u16> = (0..num_vars as u16).collect();
    for info in pred_infos.iter_mut() {
        if let LivenessPredKind::StateChangeCheck { ref mut var_indices } = info.kind {
            if var_indices.is_empty() {
                *var_indices = all_indices.clone();
                info.var_indices = all_indices.clone();
            }
        }
    }
}

/// Attempt to compile liveness predicates for the current fairness constraints.
///
/// Returns `Some(batch)` if any predicates were successfully compiled,
/// `None` if compilation is not possible (e.g., no eligible predicates,
/// no state layout available, or compilation failed).
pub(super) fn try_compile_fairness_predicates(
    state_leaves: &[LiveExpr],
    action_leaves: &[LiveExpr],
    layout: &StateLayout,
) -> Option<tla_jit::CompiledLivenessBatch> {
    let mut pred_infos = extract_pred_infos(state_leaves, action_leaves);
    if pred_infos.is_empty() {
        return None;
    }

    // Populate StateChangeCheck var_indices now that layout is available.
    populate_state_change_var_indices(&mut pred_infos, layout);

    // Check if any predicates are actually eligible
    let any_eligible = pred_infos
        .iter()
        .any(|p| !matches!(p.kind, LivenessPredKind::NotEligible));
    if !any_eligible {
        // All predicates require interpreter fallback -- no point compiling
        return None;
    }

    match tla_jit::compile_liveness_predicates(&pred_infos, layout) {
        Ok(batch) if batch.has_compiled_predicates() => {
            if crate::liveness::debug::liveness_profile() {
                eprintln!(
                    "[compiled-fairness] compiled {} state + {} action predicates \
                     ({} fallback state + {} fallback action, {} skipped) in {}us",
                    batch.stats.state_compiled,
                    batch.stats.action_compiled,
                    batch.fallback_state_tags.len(),
                    batch.fallback_action_tags.len(),
                    batch.stats.skipped_ineligible,
                    batch.stats.compile_time_us,
                );
            }
            Some(batch)
        }
        Ok(_) => None, // No predicates compiled
        Err(e) => {
            if crate::liveness::debug::liveness_profile() {
                eprintln!("[compiled-fairness] compilation failed: {e}");
            }
            None
        }
    }
}

impl ModelChecker<'_> {
    /// Part of #3992: Try to compile fairness predicates after inline fairness
    /// cache preparation. Called from `prepare_inline_fairness_cache` after
    /// the fairness leaves have been collected.
    ///
    /// This is a best-effort optimization -- if compilation fails or no
    /// predicates are eligible, the system falls back to interpreted evaluation
    /// with zero behavioral change.
    pub(in crate::check::model_checker) fn try_compile_liveness_batch(&mut self) {
        if !self.inline_fairness_active() {
            self.liveness_cache.compiled_liveness_batch = None;
            return;
        }

        // Need a state layout for compilation. If we don't have one
        // (e.g., no state variables), skip compilation.
        let layout = match self.build_liveness_state_layout() {
            Some(l) => l,
            None => {
                self.liveness_cache.compiled_liveness_batch = None;
                return;
            }
        };

        self.liveness_cache.compiled_liveness_batch = try_compile_fairness_predicates(
            &self.liveness_cache.fairness_state_checks,
            &self.liveness_cache.fairness_action_checks,
            &layout,
        );
    }

    /// Build a `StateLayout` from the model checker's variable registry.
    /// Returns `None` if the registry is empty or unavailable.
    fn build_liveness_state_layout(&self) -> Option<StateLayout> {
        let registry = self.ctx.var_registry();
        if registry.is_empty() {
            return None;
        }

        let vars: Vec<tla_jit::VarLayout> = registry
            .names()
            .iter()
            .map(|_| tla_jit::VarLayout::ScalarInt)
            .collect();

        if vars.is_empty() {
            return None;
        }

        Some(StateLayout::new(vars))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_pred_infos_empty() {
        let infos = extract_pred_infos(&[], &[]);
        assert!(infos.is_empty());
    }

    #[test]
    fn test_live_expr_enabled_not_eligible() {
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::Spanned;

        let dummy_expr = Arc::new(Spanned::new(Expr::Bool(true), Default::default()));
        let leaf = LiveExpr::enabled(dummy_expr, 5);
        let info = live_expr_to_pred_info(&leaf, true);
        assert_eq!(info.tag, 5);
        assert!(info.is_state_pred);
        assert!(matches!(info.kind, LivenessPredKind::NotEligible));
    }

    #[test]
    fn test_live_expr_state_pred_bool_not_eligible() {
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::Spanned;

        // Bool(true) is not a comparison -- should be NotEligible
        let dummy_expr = Arc::new(Spanned::new(Expr::Bool(true), Default::default()));
        let leaf = LiveExpr::state_pred(dummy_expr, 3);
        let info = live_expr_to_pred_info(&leaf, true);
        assert_eq!(info.tag, 3);
        assert!(info.is_state_pred);
        assert!(matches!(info.kind, LivenessPredKind::NotEligible));
    }

    #[test]
    fn test_analyze_state_var_eq_int() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::name_intern::NameId;
        use tla_core::Spanned;

        // x = 42 where x is StateVar at index 1
        let lhs = Box::new(Spanned::new(
            Expr::StateVar("x".to_string(), 1, NameId::INVALID),
            Default::default(),
        ));
        let rhs = Box::new(Spanned::new(
            Expr::Int(BigInt::from(42)),
            Default::default(),
        ));
        let eq_expr = Arc::new(Spanned::new(Expr::Eq(lhs, rhs), Default::default()));
        let leaf = LiveExpr::state_pred(eq_expr, 7);
        let info = live_expr_to_pred_info(&leaf, true);
        assert_eq!(info.tag, 7);
        assert!(info.is_state_pred);
        assert_eq!(info.var_indices, vec![1]);
        match info.kind {
            LivenessPredKind::ScalarComparison {
                var_idx,
                op,
                constant,
            } => {
                assert_eq!(var_idx, 1);
                assert_eq!(constant, 42);
                assert!(matches!(op, ScalarCompOp::Eq));
            }
            other => panic!("Expected ScalarComparison, got: {other:?}"),
        }
    }

    #[test]
    fn test_analyze_int_lt_state_var_flips() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::name_intern::NameId;
        use tla_core::Spanned;

        // 5 < y  should become  y > 5
        let lhs = Box::new(Spanned::new(
            Expr::Int(BigInt::from(5)),
            Default::default(),
        ));
        let rhs = Box::new(Spanned::new(
            Expr::StateVar("y".to_string(), 2, NameId::INVALID),
            Default::default(),
        ));
        let lt_expr = Arc::new(Spanned::new(Expr::Lt(lhs, rhs), Default::default()));
        let leaf = LiveExpr::state_pred(lt_expr, 10);
        let info = live_expr_to_pred_info(&leaf, true);
        assert_eq!(info.tag, 10);
        assert_eq!(info.var_indices, vec![2]);
        match info.kind {
            LivenessPredKind::ScalarComparison {
                var_idx,
                op,
                constant,
            } => {
                assert_eq!(var_idx, 2);
                assert_eq!(constant, 5);
                // Lt flipped to Gt
                assert!(matches!(op, ScalarCompOp::Gt));
            }
            other => panic!("Expected ScalarComparison, got: {other:?}"),
        }
    }

    #[test]
    fn test_analyze_var_comparison() {
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::name_intern::NameId;
        use tla_core::Spanned;

        // x >= y
        let lhs = Box::new(Spanned::new(
            Expr::StateVar("x".to_string(), 0, NameId::INVALID),
            Default::default(),
        ));
        let rhs = Box::new(Spanned::new(
            Expr::StateVar("y".to_string(), 3, NameId::INVALID),
            Default::default(),
        ));
        let geq_expr = Arc::new(Spanned::new(Expr::Geq(lhs, rhs), Default::default()));
        let leaf = LiveExpr::state_pred(geq_expr, 4);
        let info = live_expr_to_pred_info(&leaf, true);
        assert_eq!(info.tag, 4);
        assert_eq!(info.var_indices, vec![0, 3]);
        match info.kind {
            LivenessPredKind::VarComparison {
                lhs_var_idx,
                rhs_var_idx,
                op,
            } => {
                assert_eq!(lhs_var_idx, 0);
                assert_eq!(rhs_var_idx, 3);
                assert!(matches!(op, ScalarCompOp::Ge));
            }
            other => panic!("Expected VarComparison, got: {other:?}"),
        }
    }

    #[test]
    fn test_analyze_action_pred_neq() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::name_intern::NameId;
        use tla_core::Spanned;

        // x /= 0 as an action predicate
        let lhs = Box::new(Spanned::new(
            Expr::StateVar("x".to_string(), 0, NameId::INVALID),
            Default::default(),
        ));
        let rhs = Box::new(Spanned::new(
            Expr::Int(BigInt::from(0)),
            Default::default(),
        ));
        let neq_expr = Arc::new(Spanned::new(Expr::Neq(lhs, rhs), Default::default()));
        let leaf = LiveExpr::ActionPred {
            expr: neq_expr,
            bindings: None,
            tag: 2,
        };
        let info = live_expr_to_pred_info(&leaf, false);
        assert_eq!(info.tag, 2);
        assert!(!info.is_state_pred);
        match info.kind {
            LivenessPredKind::ScalarComparison {
                var_idx,
                op,
                constant,
            } => {
                assert_eq!(var_idx, 0);
                assert_eq!(constant, 0);
                assert!(matches!(op, ScalarCompOp::Ne));
            }
            other => panic!("Expected ScalarComparison, got: {other:?}"),
        }
    }

    #[test]
    fn test_flip_comparison_op() {
        assert!(matches!(flip_comparison_op(ScalarCompOp::Eq), ScalarCompOp::Eq));
        assert!(matches!(flip_comparison_op(ScalarCompOp::Ne), ScalarCompOp::Ne));
        assert!(matches!(flip_comparison_op(ScalarCompOp::Lt), ScalarCompOp::Gt));
        assert!(matches!(flip_comparison_op(ScalarCompOp::Le), ScalarCompOp::Ge));
        assert!(matches!(flip_comparison_op(ScalarCompOp::Gt), ScalarCompOp::Lt));
        assert!(matches!(flip_comparison_op(ScalarCompOp::Ge), ScalarCompOp::Le));
    }

    #[test]
    fn test_state_changed_null_subscript_no_bindings_produces_state_change_check() {
        // Null-subscript StateChanged with no bindings should produce
        // a StateChangeCheck, not NotEligible.
        let leaf = LiveExpr::StateChanged {
            subscript: None,
            bindings: None,
            tag: 8,
        };
        let info = live_expr_to_pred_info(&leaf, false);
        assert_eq!(info.tag, 8);
        assert!(!info.is_state_pred);
        match &info.kind {
            LivenessPredKind::StateChangeCheck { var_indices } => {
                // var_indices is empty as placeholder; populated by
                // populate_state_change_var_indices after layout is known.
                assert!(var_indices.is_empty());
            }
            other => panic!("Expected StateChangeCheck, got: {other:?}"),
        }
    }

    #[test]
    fn test_state_changed_with_subscript_not_eligible() {
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::Spanned;

        let sub = Arc::new(Spanned::new(Expr::Bool(true), Default::default()));
        let leaf = LiveExpr::StateChanged {
            subscript: Some(sub),
            bindings: None,
            tag: 9,
        };
        let info = live_expr_to_pred_info(&leaf, false);
        assert_eq!(info.tag, 9);
        assert!(matches!(info.kind, LivenessPredKind::NotEligible));
    }

    #[test]
    fn test_state_changed_with_bindings_not_eligible() {
        use crate::eval::{BindingChain, BindingValue};
        use tla_core::name_intern::NameId;

        let chain = BindingChain::empty()
            .cons(NameId::INVALID, BindingValue::eager(crate::Value::int(1)));
        let leaf = LiveExpr::StateChanged {
            subscript: None,
            bindings: Some(chain),
            tag: 10,
        };
        let info = live_expr_to_pred_info(&leaf, false);
        assert_eq!(info.tag, 10);
        assert!(matches!(info.kind, LivenessPredKind::NotEligible));
    }

    #[test]
    fn test_populate_state_change_var_indices_fills_empty() {
        use tla_jit::VarLayout;

        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::ScalarInt,
            VarLayout::ScalarInt,
        ]);

        let mut pred_infos = vec![
            LivenessPredInfo {
                tag: 5,
                is_state_pred: false,
                var_indices: vec![],
                kind: LivenessPredKind::StateChangeCheck {
                    var_indices: vec![],
                },
            },
            // This one should NOT be modified (already has indices).
            LivenessPredInfo {
                tag: 6,
                is_state_pred: false,
                var_indices: vec![0, 1],
                kind: LivenessPredKind::StateChangeCheck {
                    var_indices: vec![0, 1],
                },
            },
            // A non-StateChangeCheck should be untouched.
            LivenessPredInfo {
                tag: 7,
                is_state_pred: true,
                var_indices: vec![],
                kind: LivenessPredKind::NotEligible,
            },
        ];

        populate_state_change_var_indices(&mut pred_infos, &layout);

        // First entry: was empty, should now have [0, 1, 2]
        match &pred_infos[0].kind {
            LivenessPredKind::StateChangeCheck { var_indices } => {
                assert_eq!(var_indices, &[0u16, 1, 2]);
            }
            other => panic!("Expected StateChangeCheck, got: {other:?}"),
        }
        assert_eq!(pred_infos[0].var_indices, vec![0u16, 1, 2]);

        // Second entry: already had [0, 1], should be unchanged
        match &pred_infos[1].kind {
            LivenessPredKind::StateChangeCheck { var_indices } => {
                assert_eq!(var_indices, &[0u16, 1]);
            }
            other => panic!("Expected StateChangeCheck, got: {other:?}"),
        }

        // Third entry: NotEligible, untouched
        assert!(matches!(pred_infos[2].kind, LivenessPredKind::NotEligible));
    }

    #[test]
    fn test_null_subscript_state_changed_compiles_and_evaluates() {
        use tla_jit::VarLayout;

        // Build a 3-var layout and compile a null-subscript StateChanged.
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::ScalarInt,
            VarLayout::ScalarInt,
        ]);
        let action_leaves = vec![LiveExpr::StateChanged {
            subscript: None,
            bindings: None,
            tag: 3,
        }];

        let batch = try_compile_fairness_predicates(&[], &action_leaves, &layout)
            .expect("null-subscript StateChanged should compile");
        assert!(batch.action_pred_fn.is_some());
        assert_eq!(batch.compiled_action_tags, vec![3]);
        assert!(batch.fallback_action_tags.is_empty());

        // Test: no change -> false
        let current = [1i64, 2, 3];
        let next = [1i64, 2, 3];
        let result = unsafe { batch.eval_action_preds(&current, &next) };
        assert_eq!(
            result & (1 << 3),
            0,
            "identical states should not trigger StateChanged"
        );

        // Test: var changed -> true
        let next2 = [1i64, 99, 3];
        let result2 = unsafe { batch.eval_action_preds(&current, &next2) };
        assert_ne!(
            result2 & (1 << 3),
            0,
            "changed state should trigger StateChanged"
        );
    }
}
