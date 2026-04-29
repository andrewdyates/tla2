// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLCExt!Trace detection helpers.
//!
//! Recursive AST walkers that check whether an expression references `Trace`
//! (either bare `Trace` or `TLCExt!Trace`).  Extracted from `run.rs` as part
//! of #1310 (run.rs decomposition).
//!
//! Part of #1121: Shared `compute_uses_trace` detector scans invariants,
//! constraints, and action_constraints with alias awareness. All three checker
//! paths (sequential, parallel, simulation) route through this single function.

use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;

use tla_core::ast::{BoundVar, Expr, ModuleTarget, OperatorDef};

#[cfg(debug_assertions)]
use super::debug::tla2_debug;
use super::{CheckError, Config};
use crate::ConfigCheckError;

// Part of #1117: TLCExt!Trace detection - helper to check BoundVar domains
// Part of #1433: unwrap_or(false) is correct — BoundVar without a domain
// has no expression to check for Trace references. Not error-swallowing.
fn bound_var_references_trace(bound_var: &BoundVar, trace_aliases: &HashSet<String>) -> bool {
    bound_var
        .domain
        .as_ref()
        .is_some_and(|d| expr_references_trace_with_aliases(&d.node, trace_aliases))
}

// Part of #1117: TLCExt!Trace detection (test-only; production uses compute_uses_trace)
#[cfg(test)]
#[allow(dead_code)]
fn expr_references_trace(expr: &Expr) -> bool {
    expr_references_trace_with_aliases(expr, &HashSet::new())
}

/// Alias-aware trace reference detection.
///
/// Returns true if `expr` references `Trace` in any of these forms:
/// - Bare `Trace` identifier
/// - `TLCExt!Trace` (ModuleRef with Named("TLCExt"))
/// - `Alias!Trace` where `Alias` is in `trace_aliases`
fn expr_references_trace_with_aliases(expr: &Expr, trace_aliases: &HashSet<String>) -> bool {
    match expr {
        Expr::Ident(name, _) if name == "Trace" => true,
        Expr::Ident(_, _) => false,
        Expr::ModuleRef(target, op_name, args) => {
            let is_trace_ref = match target {
                ModuleTarget::Named(module_name) => {
                    op_name == "Trace"
                        && (module_name == "TLCExt" || trace_aliases.contains(module_name))
                }
                ModuleTarget::Parameterized(_, _) | ModuleTarget::Chained(_) => false,
            };
            if is_trace_ref {
                return true;
            }
            args.iter()
                .any(|arg| expr_references_trace_with_aliases(&arg.node, trace_aliases))
        }
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::OpRef(_)
        | Expr::StateVar(_, _, _) => false,
        Expr::Apply(op, args) => {
            expr_references_trace_with_aliases(&op.node, trace_aliases)
                || args
                    .iter()
                    .any(|arg| expr_references_trace_with_aliases(&arg.node, trace_aliases))
        }
        Expr::Lambda(_, body) => expr_references_trace_with_aliases(&body.node, trace_aliases),
        // Binary operators
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b) => {
            expr_references_trace_with_aliases(&a.node, trace_aliases)
                || expr_references_trace_with_aliases(&b.node, trace_aliases)
        }
        // Unary operators
        Expr::Not(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Domain(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a)
        | Expr::Neg(a) => expr_references_trace_with_aliases(&a.node, trace_aliases),
        // Quantifiers - Part of #1139: Check bound var domains (e.g., \A i \in 1..Len(Trace) : ...)
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            bounds
                .iter()
                .any(|bv| bound_var_references_trace(bv, trace_aliases))
                || expr_references_trace_with_aliases(&body.node, trace_aliases)
        }
        Expr::Choose(bound, body) => {
            bound_var_references_trace(bound, trace_aliases)
                || expr_references_trace_with_aliases(&body.node, trace_aliases)
        }
        // Collections
        Expr::SetEnum(items) | Expr::Tuple(items) | Expr::Times(items) => items
            .iter()
            .any(|item| expr_references_trace_with_aliases(&item.node, trace_aliases)),
        // Part of #1139: Check bound var domains in set builders and function definitions
        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            bounds
                .iter()
                .any(|bv| bound_var_references_trace(bv, trace_aliases))
                || expr_references_trace_with_aliases(&body.node, trace_aliases)
        }
        Expr::SetFilter(bound, body) => {
            bound_var_references_trace(bound, trace_aliases)
                || expr_references_trace_with_aliases(&body.node, trace_aliases)
        }
        Expr::Except(base, specs) => {
            expr_references_trace_with_aliases(&base.node, trace_aliases)
                || specs
                    .iter()
                    .any(|spec| expr_references_trace_with_aliases(&spec.value.node, trace_aliases))
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, value)| expr_references_trace_with_aliases(&value.node, trace_aliases)),
        Expr::RecordAccess(base, _) => {
            expr_references_trace_with_aliases(&base.node, trace_aliases)
        }
        // Control flow
        Expr::If(cond, then_e, else_e) => {
            expr_references_trace_with_aliases(&cond.node, trace_aliases)
                || expr_references_trace_with_aliases(&then_e.node, trace_aliases)
                || expr_references_trace_with_aliases(&else_e.node, trace_aliases)
        }
        Expr::Case(arms, default) => {
            arms.iter().any(|arm| {
                expr_references_trace_with_aliases(&arm.guard.node, trace_aliases)
                    || expr_references_trace_with_aliases(&arm.body.node, trace_aliases)
            }) || default
                .as_ref()
                // Part of #1433: unwrap_or(false) is correct — CASE without OTHER
                // clause has no expression to check. Not error-swallowing.
                .is_some_and(|d| expr_references_trace_with_aliases(&d.node, trace_aliases))
        }
        Expr::Let(defs, body) => {
            defs.iter()
                .any(|def| expr_references_trace_with_aliases(&def.body.node, trace_aliases))
                || expr_references_trace_with_aliases(&body.node, trace_aliases)
        }
        Expr::InstanceExpr(_, subs) => subs
            .iter()
            .any(|sub| expr_references_trace_with_aliases(&sub.to.node, trace_aliases)),
        Expr::SubstIn(subs, body) => {
            subs.iter()
                .any(|sub| expr_references_trace_with_aliases(&sub.to.node, trace_aliases))
                || expr_references_trace_with_aliases(&body.node, trace_aliases)
        }
        Expr::Label(label) => expr_references_trace_with_aliases(&label.body.node, trace_aliases),
    }
}

/// Collect TLCExt module aliases from operator definitions.
///
/// Finds zero-parameter operators whose body is `InstanceExpr("TLCExt", ...)`
/// (i.e., `Alias == INSTANCE TLCExt [WITH ...]`). Returns the set of alias names.
fn collect_trace_module_aliases<S: BuildHasher>(
    op_defs: &HashMap<String, OperatorDef, S>,
) -> HashSet<String> {
    let mut aliases = HashSet::new();
    for (name, def) in op_defs {
        if !def.params.is_empty() {
            continue;
        }
        if let Expr::InstanceExpr(module_name, _) = &def.body.node {
            if module_name == "TLCExt" {
                aliases.insert(name.clone());
            }
        }
    }
    aliases
}

/// Compute whether any configured operator references TLCExt!Trace.
///
/// Scans invariants, constraints, action_constraints, and the NEXT operator
/// for trace references, including alias forms (`Alias!Trace` where
/// `Alias == INSTANCE TLCExt`).
///
/// Returns `Err(ConfigCheckError::MissingInvariant)` or `Err(ConfigCheckError::Setup)`
/// if a configured operator name is not found in `op_defs`. This is fail-loud:
/// no silent false defaults for missing operator lookups.
///
/// Part of #1121: Single shared detector for sequential, parallel, and simulation paths.
pub(crate) fn compute_uses_trace<S: BuildHasher>(
    config: &Config,
    op_defs: &HashMap<String, OperatorDef, S>,
) -> Result<bool, CheckError> {
    let trace_aliases = collect_trace_module_aliases(op_defs);

    // Scan invariants
    for inv_name in &config.invariants {
        let def = op_defs
            .get(inv_name)
            .ok_or_else(|| ConfigCheckError::MissingInvariant(inv_name.clone()))?;
        if expr_references_trace_with_aliases(&def.body.node, &trace_aliases) {
            debug_eprintln!(
                tla2_debug(),
                "[trace-detect] TLCExt!Trace detected in invariant '{}' — trace context enabled",
                inv_name
            );
            return Ok(true);
        }
    }

    // Scan state constraints
    for constraint_name in &config.constraints {
        let def = op_defs.get(constraint_name).ok_or_else(|| {
            ConfigCheckError::Setup(format!(
                "configured CONSTRAINT '{}' not found in operator definitions",
                constraint_name
            ))
        })?;
        if expr_references_trace_with_aliases(&def.body.node, &trace_aliases) {
            debug_eprintln!(
                tla2_debug(),
                "[trace-detect] TLCExt!Trace detected in CONSTRAINT '{}' — trace context enabled",
                constraint_name
            );
            return Ok(true);
        }
    }

    // Scan action constraints
    for ac_name in &config.action_constraints {
        let def = op_defs.get(ac_name).ok_or_else(|| {
            ConfigCheckError::Setup(format!(
                "configured ACTION_CONSTRAINT '{}' not found in operator definitions",
                ac_name
            ))
        })?;
        if expr_references_trace_with_aliases(&def.body.node, &trace_aliases) {
            debug_eprintln!(
                tla2_debug(),
                "[trace-detect] TLCExt!Trace detected in ACTION_CONSTRAINT '{}' — trace context enabled",
                ac_name
            );
            return Ok(true);
        }
    }

    // Scan NEXT operator (including inline NEXT registered under INLINE_NEXT_NAME).
    // TLCExt!Trace in the NEXT expression requires full-state storage.
    if let Some(next_name) = &config.next {
        if let Some(def) = op_defs.get(next_name) {
            if expr_references_trace_with_aliases(&def.body.node, &trace_aliases) {
                debug_eprintln!(
                    tla2_debug(),
                    "[trace-detect] TLCExt!Trace detected in NEXT operator — trace context enabled"
                );
                return Ok(true);
            }
        }
    }

    Ok(false)
}

// TODO(W3): test file not yet created — uncomment when trace_detect_tests.rs exists
// #[cfg(test)]
// mod trace_detect_tests;
