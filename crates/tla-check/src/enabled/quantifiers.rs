// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier handlers for ENABLED constraint propagation.
//!
//! Handles `\E x \in S : P` and `\A x \in S : P` with recursive
//! multi-bound support (#3035).
//!
//! Part of #3004: ENABLED constraint propagation decision procedure.

use super::dispatch::{dispatch_enabled, eval_as_bool, CpResult};
use super::set_enumerate::enumerate_set_in_ctx;
use super::witness_state::WitnessState;
use crate::eval::{eval, EvalCtx};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Spanned, VarRegistry};

/// Handle `\E x \in S : P` — existential quantification.
///
/// TLC: Tool.java:3146-3159
///
/// Fix for #3030: Uses `enumerate_set_in_ctx` to handle SetPred domains
/// (lazy predicate-filtered sets like `{f \in S : P(f)}`). SetPred values
/// cannot be iterated via `Value::iter_set()` and their standard
/// materialization path (`eval_iter_set`) restores a captured context that
/// loses the ENABLED scope's LET bindings. By enumerating the SetPred's
/// source set and evaluating the predicate in the current ctx, we preserve
/// all bindings from handle_let (e.g., `senders(v)` in local_ops).
pub(super) fn handle_exists(
    ctx: &EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    body: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    // #3035: Process bounds recursively to support multi-bound quantifiers
    // without falling back to eval_as_bool (which loses witness state).
    handle_exists_recursive(ctx, bounds, body, registry, witness)
}

/// Recursively peel off one bound at a time for existential quantification.
///
/// `\E x \in S, y \in T : P(x, y)` becomes `\E x \in S : \E y \in T : P(x, y)`.
fn handle_exists_recursive(
    ctx: &EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    body: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    if bounds.is_empty() {
        return dispatch_enabled(ctx, body, registry, witness);
    }

    let bound = &bounds[0];
    if let Some(domain_expr) = &bound.domain {
        let domain_val = eval(ctx, domain_expr)?;
        let members = enumerate_set_in_ctx(ctx, &domain_val, Some(domain_expr.span))?;
        for member in members {
            let mut inner_ctx = ctx.clone();
            let _guard = inner_ctx.scope_guard();
            inner_ctx.bind_mut(Arc::from(bound.name.node.as_str()), member);
            let result =
                handle_exists_recursive(&inner_ctx, &bounds[1..], body, registry, witness.clone())?;
            if result.is_some() {
                return Ok(result);
            }
        }
        return Ok(None);
    }

    // Unbounded: fall back to evaluating the full expression
    eval_as_bool(
        ctx,
        &Spanned::new(
            Expr::Exists(bounds.to_vec(), Box::new(body.clone())),
            body.span,
        ),
        witness,
        registry,
    )
}

/// Handle `\A x \in S : P` — universal quantification.
///
/// Uses `enumerate_set_in_ctx` for SetPred support (same as handle_exists).
pub(super) fn handle_forall(
    ctx: &EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    body: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    // #3035: Process bounds recursively to support multi-bound quantifiers.
    handle_forall_recursive(ctx, bounds, body, registry, witness)
}

/// Recursively peel off one bound at a time for universal quantification.
fn handle_forall_recursive(
    ctx: &EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    body: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    if bounds.is_empty() {
        return dispatch_enabled(ctx, body, registry, witness);
    }

    let bound = &bounds[0];
    if let Some(domain_expr) = &bound.domain {
        let domain_val = eval(ctx, domain_expr)?;
        let members = enumerate_set_in_ctx(ctx, &domain_val, Some(domain_expr.span))?;
        let mut current_witness = witness;
        for member in members {
            let mut inner_ctx = ctx.clone();
            let _guard = inner_ctx.scope_guard();
            inner_ctx.bind_mut(Arc::from(bound.name.node.as_str()), member);
            match handle_forall_recursive(
                &inner_ctx,
                &bounds[1..],
                body,
                registry,
                current_witness,
            )? {
                Some(w) => current_witness = w,
                None => return Ok(None),
            }
        }
        return Ok(Some(current_witness));
    }

    // Unbounded: fall back to evaluating the full expression
    eval_as_bool(
        ctx,
        &Spanned::new(
            Expr::Forall(bounds.to_vec(), Box::new(body.clone())),
            body.span,
        ),
        witness,
        registry,
    )
}
