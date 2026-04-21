// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conjunction processing with backtracking for ENABLED constraint propagation.
//!
//! Flattens nested `/\` into a list and processes with an index so that
//! domain enumeration (`x' \in S`) backtracks through remaining conjuncts.
//!
//! Part of #3004: ENABLED constraint propagation decision procedure.

use super::dispatch::{
    dispatch_enabled, get_primed_var_idx, handle_equality_leaf, handle_unchanged, CpResult,
};
use super::quantifiers::handle_exists;
use super::witness_state::WitnessState;
use crate::eval::{eval, EvalCtx};
use tla_core::ast::Expr;
use tla_core::{Spanned, VarRegistry};

/// Flatten nested `And` nodes into a list of conjuncts.
pub(super) fn flatten_conjunction<'a>(expr: &'a Spanned<Expr>, out: &mut Vec<&'a Spanned<Expr>>) {
    match &expr.node {
        Expr::And(a, b) => {
            flatten_conjunction(a, out);
            flatten_conjunction(b, out);
        }
        _ => out.push(expr),
    }
}

/// Process a flat list of conjuncts with backtracking for domain enumeration.
///
/// When `x' \in S` introduces a domain binding, tries each element and
/// continues with remaining conjuncts. Later conjunct failure triggers
/// backtracking to the next domain element.
pub(super) fn process_conjuncts(
    ctx: &EvalCtx,
    conjuncts: &[&Spanned<Expr>],
    start: usize,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    if start >= conjuncts.len() {
        return Ok(Some(witness));
    }

    let expr = conjuncts[start];

    // Check for primed variable membership first to avoid double-call TOCTOU pattern.
    if let Expr::In(elem, set) = &expr.node {
        if let Some(var_idx) = get_primed_var_idx(&elem.node, registry) {
            return handle_membership_conjunct(
                ctx,
                var_idx,
                set,
                conjuncts,
                start + 1,
                registry,
                witness,
            );
        }
    }

    match &expr.node {
        Expr::Eq(lhs, rhs) => {
            let result = handle_equality_leaf(ctx, lhs, rhs, registry, witness)?;
            match result {
                Some(w) => process_conjuncts(ctx, conjuncts, start + 1, registry, w),
                None => Ok(None),
            }
        }

        Expr::Unchanged(vars_expr) => {
            let result = handle_unchanged(ctx, vars_expr, registry, witness)?;
            match result {
                Some(w) => process_conjuncts(ctx, conjuncts, start + 1, registry, w),
                None => Ok(None),
            }
        }

        Expr::Exists(bounds, body) => {
            let result = handle_exists(ctx, bounds, body, registry, witness)?;
            match result {
                Some(w) => process_conjuncts(ctx, conjuncts, start + 1, registry, w),
                None => Ok(None),
            }
        }

        _ => {
            let result = dispatch_enabled(ctx, expr, registry, witness)?;
            match result {
                Some(w) => process_conjuncts(ctx, conjuncts, start + 1, registry, w),
                None => Ok(None),
            }
        }
    }
}

/// Handle `x' \in S` inside a conjunction with backtracking.
///
/// When x' is unbound, enumerates S members and tries each with remaining
/// conjuncts. This is the critical backtracking point.
fn handle_membership_conjunct(
    ctx: &EvalCtx,
    var_idx: usize,
    set: &Spanned<Expr>,
    conjuncts: &[&Spanned<Expr>],
    cont_start: usize,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    match witness.lookup(var_idx) {
        Some(existing) => {
            let set_val = eval(ctx, set)?;
            let is_member = set_val.set_contains(existing).unwrap_or(false);
            if is_member {
                process_conjuncts(ctx, conjuncts, cont_start, registry, witness)
            } else {
                Ok(None)
            }
        }
        None => {
            let set_val = eval(ctx, set)?;
            if let Some(iter) = set_val.iter_set() {
                for member in iter {
                    let w = witness.bind(var_idx, member);
                    let result = process_conjuncts(ctx, conjuncts, cont_start, registry, w)?;
                    if result.is_some() {
                        return Ok(result);
                    }
                }
            }
            Ok(None)
        }
    }
}
