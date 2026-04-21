// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fairness constraint to LiveExpr conversion.
//!
//! Part of #2740: extracted from `checker_ops.rs` to prevent parity drift
//! between sequential and parallel checker paths.

use crate::eval::EvalCtx;
use crate::liveness::{ActionPredHint, AstToLive, LiveExpr};
use crate::spec_formula::FairnessConstraint;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_core::Spanned;

/// Error during fairness constraint to LiveExpr conversion.
#[derive(Debug, thiserror::Error)]
pub(crate) enum FairnessToLiveExprError {
    #[error("{}", .0)]
    Convert(
        #[source]
        #[from]
        Box<FairnessConvertDetail>,
    ),
    #[error("{0}")]
    Other(String),
}

#[derive(Debug, thiserror::Error)]
#[error("{context}: {error}")]
pub(crate) struct FairnessConvertDetail {
    pub(crate) context: String,
    #[source]
    pub(crate) error: crate::liveness::ConvertError,
}

/// Convert a `FairnessConstraint` to a `LiveExpr`.
///
/// This is the canonical implementation used by both the sequential and parallel
/// checker paths. The sequential checker delegates through `ModelChecker::fairness_to_live_expr`.
///
/// WF_vars(Action) becomes `[]<>(~ENABLED(<<A>>_vars) \/ <<A>>_vars)`
/// SF_vars(Action) becomes `<>[]~ENABLED(<<A>>_vars) \/ []<><<A>>_vars`
/// TemporalRef directly converts the referenced operator's body to LiveExpr.
/// QuantifiedTemporal lowers the inline syntax node and converts.
pub(crate) fn fairness_to_live_expr(
    constraint: &FairnessConstraint,
    op_defs: &FxHashMap<String, OperatorDef>,
    ctx: &EvalCtx,
    converter: &AstToLive,
) -> Result<LiveExpr, FairnessToLiveExprError> {
    // Handle TemporalRef separately - it directly converts the operator body
    if let FairnessConstraint::TemporalRef { op_name } = constraint {
        let def = op_defs.get(op_name).ok_or_else(|| {
            FairnessToLiveExprError::Other(format!(
                "Operator '{}' not found for temporal reference",
                op_name
            ))
        })?;
        return converter.convert(ctx, &def.body).map_err(|e| {
            FairnessToLiveExprError::Convert(Box::new(FairnessConvertDetail {
                context: format!("Failed to convert temporal formula '{}'", op_name),
                error: e,
            }))
        });
    }

    // Handle QuantifiedTemporal - inline quantified fairness from spec body
    if let FairnessConstraint::QuantifiedTemporal { node } = constraint {
        let expr = tla_core::lower_single_expr(tla_core::FileId(0), node).ok_or_else(|| {
            FairnessToLiveExprError::Other(
                "Failed to lower inline quantified temporal formula".to_string(),
            )
        })?;
        let spanned = Spanned::dummy(expr);
        return converter.convert(ctx, &spanned).map_err(|e| {
            FairnessToLiveExprError::Convert(Box::new(FairnessConvertDetail {
                context: "Failed to convert quantified temporal formula".to_string(),
                error: e,
            }))
        });
    }

    let (is_weak, action_name, action_node, vars_name) = match constraint {
        FairnessConstraint::Weak {
            action,
            action_node,
            vars,
        } => (true, action, action_node, vars),
        FairnessConstraint::Strong {
            action,
            action_node,
            vars,
        } => (false, action, action_node, vars),
        FairnessConstraint::TemporalRef { .. } | FairnessConstraint::QuantifiedTemporal { .. } => {
            unreachable!("Handled above")
        }
    };

    // Get the action expression body either from op_defs or by lowering the inline expression
    let action_body: Spanned<tla_core::ast::Expr> = if let Some(def) = op_defs.get(action_name) {
        def.body.clone()
    } else if let Some(node) = action_node {
        let expr = tla_core::lower_single_expr(tla_core::FileId(0), node).ok_or_else(|| {
            FairnessToLiveExprError::Other(format!(
                "Failed to lower inline action expression for fairness constraint: {}",
                action_name
            ))
        })?;
        Spanned::dummy(expr)
    } else {
        return Err(FairnessToLiveExprError::Other(format!(
            "Action '{}' not found for fairness constraint",
            action_name
        )));
    };

    // Get the subscript expression (vars) - used for stuttering check
    let subscript_expr: Option<Arc<Spanned<tla_core::ast::Expr>>> =
        if let Some(def) = op_defs.get(vars_name) {
            Some(Arc::new(def.body.clone()))
        } else if vars_name.starts_with("<<") {
            // vars_name is a tuple expression like "<<coordinator, participant>>"
            let inner = vars_name.trim_start_matches("<<").trim_end_matches(">>");
            let var_names: Vec<_> = inner
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .collect();
            let tuple_elems: Vec<_> = var_names
                .iter()
                .map(|vn| {
                    Spanned::dummy(tla_core::ast::Expr::Ident(
                        (*vn).into(),
                        tla_core::name_intern::NameId::INVALID,
                    ))
                })
                .collect();
            Some(Arc::new(Spanned::dummy(tla_core::ast::Expr::Tuple(
                tuple_elems,
            ))))
        } else {
            Some(Arc::new(Spanned::dummy(tla_core::ast::Expr::Ident(
                vars_name.clone(),
                tla_core::name_intern::NameId::INVALID,
            ))))
        };

    // Resolve operator references in the action expression (critical for LET bindings, #233)
    let resolved_action_body = converter.resolve_action_expr(ctx, &action_body);

    // Resolve the subscript expression as well
    let resolved_subscript_expr =
        subscript_expr.map(|s| Arc::new(converter.resolve_action_expr(ctx, &s)));

    // Convert action to LiveExpr (as an action predicate)
    let action_live = match converter.convert(ctx, &action_body) {
        Ok(live) => live,
        Err(e) => {
            return Err(FairnessToLiveExprError::Convert(Box::new(
                FairnessConvertDetail {
                    context: format!("Failed to convert action '{}' for fairness", action_name),
                    error: e,
                },
            )));
        }
    };

    // Part of #3100: Record action hint for provenance matching.
    // For simple actions, the convert result is a single ActionPred with a tag.
    // Config-driven fairness uses name-only hints (no actual-arg bindings).
    if let LiveExpr::ActionPred { tag, .. } = &action_live {
        // Wrapper actions like `Schedule == /\ Sched!Schedule /\ UNCHANGED ...`
        // still need name-based provenance for diagnostics, but the split-action
        // fast path is too coarse once the resolved body crosses an INSTANCE
        // boundary (#3161).
        let split_action_fast_path_safe = !super::contains_module_ref(&resolved_action_body.node);
        converter.record_action_hint(ActionPredHint {
            tag: *tag,
            name: Arc::from(action_name.as_str()),
            split_action_fast_path_safe,
            actual_arg_bindings: Vec::new(),
        });
    }

    // Create ENABLED(<<A>>_vars) predicate
    // IMPORTANT: Use resolved_action_body, not original action_body (issue #233)
    let enabled = LiveExpr::enabled_subscripted(
        Arc::new(resolved_action_body),
        resolved_subscript_expr.clone(),
        converter.alloc_tag(),
    );

    // Create subscripted action <<A>>_vars = A /\ (vars' ≠ vars)
    let state_changed = LiveExpr::state_changed(resolved_subscript_expr, converter.alloc_tag());
    let subscripted_action = LiveExpr::and(vec![action_live, state_changed]);

    if is_weak {
        // WF_vars(Action): []<>(~ENABLED(<<A>>_vars) \/ <<A>>_vars)
        let not_enabled = LiveExpr::not(enabled);
        let disj = LiveExpr::or(vec![not_enabled, subscripted_action]);
        Ok(LiveExpr::always(LiveExpr::eventually(disj)))
    } else {
        // SF_vars(Action): <>[]~ENABLED(<<A>>_vars) \/ []<><<A>>_vars
        let not_enabled = LiveExpr::not(enabled);
        let eventually_always_disabled = LiveExpr::eventually(LiveExpr::always(not_enabled));
        let infinitely_often = LiveExpr::always(LiveExpr::eventually(subscripted_action));
        Ok(LiveExpr::or(vec![
            eventually_always_disabled,
            infinitely_often,
        ]))
    }
}
