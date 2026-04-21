// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thin adapter dispatching array-containing SMT queries to z4-dpll's Executor.
//!
//! When the CHC solver's internal DPLL(T) loop (`check_sat.rs`) encounters
//! formulas with array operations (select, store, const-array), the loop lacks
//! proper array axiom generation and returns Unknown. This adapter converts the
//! ChcExpr to SMT-LIB text and delegates to z4-dpll's Executor, which has full
//! array theory support (eager axioms, extensionality, ROW lemmas, N-O fixpoint).
//!
//! Design: `designs/2026-03-07-issue-6047-dpll-t-array-theory-integration.md`
//! Approach C — thin adapter, array logics only.

mod logic_detection;
mod model_parsing;

// Re-export for sibling modules (persistent.rs) and crate-level re-export (smt/mod.rs #7983).
pub(crate) use logic_detection::{
    collect_dt_declarations, detect_logic, emit_declare_datatype, quote_symbol, sort_to_smtlib,
};
pub(crate) use model_parsing::parse_model_into;

// Re-export test-visible helpers (tests.rs uses super::*).
#[cfg(test)]
pub(super) use model_parsing::{
    parse_decimal_to_rational, parse_model_simple, parse_simple_value, term_body_to_smt_value,
};

use super::context::SmtContext;
use super::model_verify::verify_sat_model_conjunction_strict_with_mod_retry;
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::pdr::model::InvariantModel;
use crate::ChcExpr;
use rustc_hash::{FxHashMap, FxHashSet};
use std::panic::AssertUnwindSafe;

fn execute_commands_via_executor(commands: &[z4_frontend::Command]) -> Result<Vec<String>, ()> {
    let mut exec = z4_dpll::Executor::new();
    z4_core::catch_z4_panics(
        AssertUnwindSafe(|| match exec.execute_all(commands) {
            Ok(out) => Ok(out),
            Err(e) => {
                tracing::debug!("executor_adapter: execution error: {e}");
                Err(())
            }
        }),
        |reason| {
            tracing::debug!("executor_adapter: z4 panic: {reason}");
            Err(())
        },
    )
}

fn needs_strict_reparsed_validation(exprs: &[&ChcExpr]) -> bool {
    exprs
        .iter()
        .any(|expr| expr.contains_array_ops() || expr.contains_dt_ops() || expr.has_mod_aux_vars())
}

pub(super) fn accept_reparsed_sat_model(
    exprs: &[&ChcExpr],
    model: FxHashMap<String, SmtValue>,
    source: &'static str,
) -> Option<FxHashMap<String, SmtValue>> {
    let verify_result =
        verify_sat_model_conjunction_strict_with_mod_retry(exprs.iter().copied(), &model);
    let requires_strict = needs_strict_reparsed_validation(exprs);

    match verify_result {
        ModelVerifyResult::Invalid => {
            tracing::warn!(
                "{source}: reparsed SAT model violates original CHC expression; returning Unknown"
            );
            None
        }
        ModelVerifyResult::Indeterminate if requires_strict => {
            tracing::debug!(
                "{source}: reparsed SAT model is indeterminate for array/DT/mod query; returning Unknown"
            );
            None
        }
        ModelVerifyResult::Indeterminate => {
            tracing::debug!("{source}: reparsed SAT model verification indeterminate; accepting");
            Some(model)
        }
        ModelVerifyResult::Valid => {
            debug_assert!(
                !requires_strict || matches!(verify_result, ModelVerifyResult::Valid),
                "BUG: reparsed SAT model for array/DT/mod query must validate before acceptance"
            );
            Some(model)
        }
    }
}

impl SmtContext {
    /// Dispatch an array-containing formula to z4-dpll's Executor for full
    /// array theory support. Falls back to SmtResult::Unknown on any error.
    ///
    /// The `propagated_model` contains var=value bindings discovered during
    /// preprocessing (constant propagation, singleton bounds). These are merged
    /// into the executor's model on Sat so PDR cube extraction has access to all
    /// known bindings.
    pub(crate) fn check_sat_via_executor(
        &self,
        expr: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: std::time::Duration,
    ) -> SmtResult {
        // Step 1: Collect free variables and their sorts from the expression.
        let vars = expr.vars();
        if vars.is_empty() {
            // No variables -- constant expression. Let the normal path handle it.
            return SmtResult::Unknown;
        }

        // Step 2: Detect the appropriate logic based on sorts present.
        let logic = detect_logic(&vars, expr);

        // Step 3: Build SMT-LIB text.
        let mut smt = String::with_capacity(512);
        smt.push_str(&format!("(set-logic {logic})\n"));
        smt.push_str("(set-option :produce-models true)\n");

        // Set timeout if available -- z4-dpll uses :timeout option in ms.
        let timeout_ms = timeout.as_millis();
        if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
            smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
        }

        // Declare datatypes before any constants that use them.
        let dt_decls = collect_dt_declarations(&vars);
        for (dt_name, ctors) in &dt_decls {
            smt.push_str(&emit_declare_datatype(dt_name, ctors));
        }

        // Declare variables.
        for var in &vars {
            let sort_str = sort_to_smtlib(&var.sort);
            let name = quote_symbol(&var.name);
            smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
        }

        // Assert the formula. Split top-level conjunctions into separate
        // (assert ...) statements so z4-dpll's DT axiom generation sees each
        // conjunct individually. Without this, (assert (and A B C)) hides
        // DT constructor equalities from the reachability filter (#7016).
        let conjuncts = expr.conjuncts();
        for c in &conjuncts {
            let c_str = InvariantModel::expr_to_smtlib(c);
            smt.push_str(&format!("(assert {c_str})\n"));
        }
        smt.push_str("(check-sat)\n");
        smt.push_str("(get-model)\n");

        // Step 4: Parse and execute via z4-dpll.
        let commands = match z4_frontend::parse(&smt) {
            Ok(cmds) => cmds,
            Err(e) => {
                tracing::debug!("executor_adapter: parse error: {e}");
                return SmtResult::Unknown;
            }
        };

        let outputs = match execute_commands_via_executor(&commands) {
            Ok(out) => out,
            Err(()) => return SmtResult::Unknown,
        };

        // Step 5: Interpret the result.
        let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
        match result_str {
            "unsat" => SmtResult::Unsat,
            "sat" => {
                // Parse model from the second output (get-model response).
                let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
                let mut model = propagated_model.clone();
                let dt_ctor_names: FxHashSet<String> = dt_decls
                    .iter()
                    .flat_map(|(_, ctors)| ctors.iter().map(|c| c.name.clone()))
                    .collect();
                parse_model_into(&mut model, model_str, &dt_ctor_names);
                let validation_exprs = [expr];
                if let Some(model) =
                    accept_reparsed_sat_model(&validation_exprs, model, "executor_adapter")
                {
                    SmtResult::Sat(model)
                } else {
                    SmtResult::Unknown
                }
            }
            "unknown" => SmtResult::Unknown,
            other => {
                tracing::warn!(
                    "executor_adapter: unexpected result string: {other:?}, treating as Unknown"
                );
                SmtResult::Unknown
            }
        }
    }
}

/// Dispatch a conjunction of expressions (background + assumptions) to z4-dpll's
/// Executor for full array theory support. Used by `IncrementalSatContext` when
/// the internal DPLL(T) loop returns Unknown on array-containing formulas.
///
/// Combines all expressions into a single `(and ...)` assertion and runs it
/// through the executor. Returns `IncrementalCheckResult` matching the caller's
/// expected return type.
pub(crate) fn check_sat_conjunction_via_executor(
    exprs: &[ChcExpr],
    propagated_equalities: &FxHashMap<String, i64>,
    timeout: std::time::Duration,
) -> super::incremental::IncrementalCheckResult {
    use super::incremental::IncrementalCheckResult;

    // Collect all free variables across all expressions for declarations.
    let combined = ChcExpr::and_all(exprs.iter().cloned());
    let vars = combined.vars();
    if vars.is_empty() {
        return IncrementalCheckResult::Unknown;
    }

    let logic = detect_logic(&vars, &combined);

    let mut smt = String::with_capacity(1024);
    smt.push_str(&format!("(set-logic {logic})\n"));
    smt.push_str("(set-option :produce-models true)\n");

    let timeout_ms = timeout.as_millis();
    if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
        smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    }

    // Declare datatypes before any constants that use them.
    let dt_decls = collect_dt_declarations(&vars);
    for (dt_name, ctors) in &dt_decls {
        smt.push_str(&emit_declare_datatype(dt_name, ctors));
    }

    for var in &vars {
        let sort_str = sort_to_smtlib(&var.sort);
        let name = quote_symbol(&var.name);
        smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
    }

    // Assert each expression separately, splitting top-level conjunctions
    // into individual asserts for DT axiom reachability (#7016).
    for expr in exprs {
        let conjuncts = expr.conjuncts();
        for c in &conjuncts {
            let c_str = InvariantModel::expr_to_smtlib(c);
            smt.push_str(&format!("(assert {c_str})\n"));
        }
    }
    smt.push_str("(check-sat)\n");
    smt.push_str("(get-model)\n");

    let commands = match z4_frontend::parse(&smt) {
        Ok(cmds) => cmds,
        Err(e) => {
            tracing::debug!("executor_adapter (incremental): parse error: {e}");
            return IncrementalCheckResult::Unknown;
        }
    };

    let outputs = match execute_commands_via_executor(&commands) {
        Ok(out) => out,
        Err(()) => return IncrementalCheckResult::Unknown,
    };

    let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
    match result_str {
        "unsat" => IncrementalCheckResult::Unsat,
        "sat" => {
            let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
            let mut model = FxHashMap::default();
            // Merge propagated equalities into model.
            for (name, value) in propagated_equalities {
                model.insert(name.clone(), SmtValue::Int(*value));
            }
            let dt_ctor_names: FxHashSet<String> = dt_decls
                .iter()
                .flat_map(|(_, ctors)| ctors.iter().map(|c| c.name.clone()))
                .collect();
            parse_model_into(&mut model, model_str, &dt_ctor_names);
            let validation_exprs: Vec<&ChcExpr> = exprs.iter().collect();
            if let Some(model) = accept_reparsed_sat_model(
                &validation_exprs,
                model,
                "executor_adapter (incremental)",
            ) {
                IncrementalCheckResult::Sat(model)
            } else {
                IncrementalCheckResult::Unknown
            }
        }
        "unknown" => IncrementalCheckResult::Unknown,
        other => {
            tracing::warn!(
                "executor_adapter (incremental): unexpected result string: {other:?}, treating as Unknown"
            );
            IncrementalCheckResult::Unknown
        }
    }
}

#[cfg(test)]
mod tests;
