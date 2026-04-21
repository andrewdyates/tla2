// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Safety-temporal fast path classification.
//!
//! Extracts the property classification logic from
//! `ModelChecker::check_safety_temporal_property` into a free function
//! usable by both the sequential and parallel checkers.
//!
//! Part of #2892: the parallel checker was missing this fast path,
//! sending all `[]P` properties through the expensive Tableau+SCC pipeline.

use crate::check::{check_error_to_result, CheckError, CheckStats};
use crate::eval::EvalCtx;
use crate::EvalCheckError;
use crate::Value;
use rustc_hash::FxHashMap;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::Spanned;

use super::{plan_property_terms, PlannedPropertyTerm};

/// Evaluate a property term expression and require a boolean result.
///
/// This is the **canonical** property-term boolean evaluation function shared by
/// both the sequential and parallel post-BFS liveness paths. Both paths MUST call
/// this function for all property-term evaluation to prevent parity drift.
///
/// Returns `Ok(true/false)` on successful boolean evaluation, or `Err(CheckError)`
/// on non-boolean result or evaluation error.
///
/// Part of #3716: extracted from three duplicated call sites:
/// - `ModelChecker::eval_property_bool_term` (safety_temporal.rs)
/// - `ModelChecker::eval_safety_part_bool_term` (safety_parts.rs)
/// - Inline expansion in `ParallelChecker::check_safety_temporal_terms` (liveness_safety.rs)
pub(crate) fn eval_property_bool_term(
    ctx: &EvalCtx,
    prop_name: &str,
    term: &Spanned<Expr>,
) -> Result<bool, CheckError> {
    match crate::eval::eval_entry(ctx, term) {
        Ok(Value::Bool(value)) => Ok(value),
        Ok(_) => Err(EvalCheckError::PropertyNotBoolean(prop_name.to_string()).into()),
        Err(error) => Err(EvalCheckError::Eval(error).into()),
    }
}

/// Evaluate a property term and convert errors to `CheckResult` for post-BFS callers.
///
/// Thin wrapper around [`eval_property_bool_term`] that maps `CheckError` through
/// `check_error_to_result` for callers that need a `CheckResult` on failure.
///
/// Part of #3716: replaces the duplicated method bodies in both checkers.
pub(crate) fn eval_property_bool_term_to_result(
    ctx: &EvalCtx,
    prop_name: &str,
    term: &Spanned<Expr>,
    stats: &CheckStats,
) -> Result<bool, crate::check::CheckResult> {
    eval_property_bool_term(ctx, prop_name, term)
        .map_err(|error| check_error_to_result(error, stats))
}

/// Result of classifying a property for the safety-temporal fast path.
#[derive(Debug)]
pub(crate) enum SafetyTemporalClassification {
    /// Property contains temporal operators — must use full Tableau+SCC
    /// liveness checking.
    NotApplicable,
    /// Property is decomposable into safety-temporal terms that can be
    /// checked by iterating the state graph directly.
    Applicable {
        /// Non-Always terms to check on initial states only.
        init_terms: Vec<Spanned<Expr>>,
        /// `[]P` terms where P is state/constant level — check on each state.
        always_state_terms: Vec<Spanned<Expr>>,
        /// `[]A` terms where A is action level — check on each transition.
        always_action_terms: Vec<Spanned<Expr>>,
    },
}

/// Classify a temporal property for the safety-temporal fast path.
///
/// Determines whether a property is a conjunction of:
/// - State-level terms (checked on initial states)
/// - `[]P` terms where P has no temporal operators (checked on states/transitions)
///
/// If so, returns `Applicable` with the decomposed terms. Otherwise returns
/// `NotApplicable`, indicating the caller should use full Tableau+SCC.
///
/// This is the shared classification logic extracted from
/// `ModelChecker::check_safety_temporal_property` (safety_temporal.rs:71-231).
/// Both sequential and parallel checkers can use this.
///
/// Part of #2892.
pub(crate) fn classify_safety_temporal(
    ctx: &EvalCtx,
    op_defs: &FxHashMap<String, OperatorDef>,
    prop_name: &str,
) -> SafetyTemporalClassification {
    let Some(plan) = plan_property_terms(ctx, op_defs, prop_name) else {
        return SafetyTemporalClassification::NotApplicable;
    };

    let mut init_terms = Vec::new();
    let mut always_state_terms: Vec<Spanned<Expr>> = Vec::new();
    let mut always_action_terms: Vec<Spanned<Expr>> = Vec::new();
    for term in plan.terms {
        match term {
            PlannedPropertyTerm::Init(body) => init_terms.push(body),
            PlannedPropertyTerm::StateCompiled(body) | PlannedPropertyTerm::StateEval(body) => {
                always_state_terms.push(body);
            }
            PlannedPropertyTerm::ActionCompiled(body) | PlannedPropertyTerm::ActionEval(body) => {
                always_action_terms.push(body);
            }
            PlannedPropertyTerm::Liveness(_) => {
                return SafetyTemporalClassification::NotApplicable;
            }
        }
    }
    if always_state_terms.is_empty() && always_action_terms.is_empty() {
        return SafetyTemporalClassification::NotApplicable;
    }

    SafetyTemporalClassification::Applicable {
        init_terms,
        always_state_terms,
        always_action_terms,
    }
}

/// Returns true if any configured PROPERTY requires the full SCC-based liveness
/// checker (i.e., has genuine temporal content beyond top-level `[]P`).
///
/// Properties that are pure conjunctions of `[]P` (where P is state/action-level)
/// and state-level init terms are handled by the safety-temporal fast path and
/// do NOT require the liveness checker. This distinction matters for the
/// SYMMETRY+PROPERTY+notrace guard: pure safety properties work fine in notrace
/// mode even with symmetry, but genuine temporal properties (WF, SF, <>, ~>)
/// need full-state mode for sound liveness checking.
///
/// Part of #2227: Prevents over-rejection of SYMMETRY+PROPERTY+notrace when all
/// properties are pure safety.
pub fn any_property_requires_liveness_checker(
    ctx: &EvalCtx,
    op_defs: &FxHashMap<String, OperatorDef>,
    properties: &[String],
) -> bool {
    for prop_name in properties {
        if matches!(
            classify_safety_temporal(ctx, op_defs, prop_name),
            SafetyTemporalClassification::NotApplicable
        ) {
            return true;
        }
    }
    false
}
