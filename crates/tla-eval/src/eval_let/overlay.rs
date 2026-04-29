// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! All-zero-arg `LetDefOverlay` fast path for LET expressions.
//!
//! Handles simple scalars, recursive FuncDefs, and InstanceExprs without
//! cloning OpEnv. Matches TLC's Context.cons model (Tool.java:1848-1860).
//!
//! Extracted from `eval_let.rs` for file size compliance (#3474).

use super::eval_let_func_domain;
use super::zero_arg_cache::eval_zero_arg_let_body;
use crate::error::{EvalError, EvalResult};
use crate::eval;
use crate::value::{LazyDomain, Value};
use crate::EvalCtx;
use std::sync::Arc;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::{expr_mentions_name_v, Span, Spanned};

use super::build_lazy_func_from_ctx;

/// Part of #1093: Fast path for all-zero-arg LET blocks using LetDefOverlay.
/// Returns `Some(result)` on success, `None` if fallthrough needed (eager eval failed).
pub(super) fn eval_let_all_zero_arg(
    ctx: &EvalCtx,
    defs: &[OperatorDef],
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> Option<EvalResult<Value>> {
    // Safety: InstanceExpr + recursive FuncDef coexistence → fall through.
    // LazyFunc captures don't preserve the overlay, so module refs from
    // inside the recursive body would fail to find the instance def.
    if defs
        .iter()
        .any(|d| matches!(&d.body.node, Expr::InstanceExpr(_, _)))
        && defs.iter().any(|d| {
            matches!(&d.body.node, Expr::FuncDef(_, fb)
                if expr_mentions_name_v(&fb.node, d.name.node.as_str()))
        })
    {
        return None;
    }
    let mut bound_ctx = ctx.clone();
    for def in defs {
        if matches!(&def.body.node, Expr::InstanceExpr(_, _)) {
            let name: Arc<str> = Arc::from(def.name.node.as_str());
            bound_ctx.let_def_overlay = bound_ctx.let_def_overlay.cons(name, Arc::new(def.clone()));
            continue;
        }
        if let Expr::FuncDef(bounds, func_body) = &def.body.node {
            if expr_mentions_name_v(&func_body.node, def.name.node.as_str()) {
                let name: Arc<str> = Arc::from(def.name.node.as_str());
                // Overlay first (for self-recursion via get_op), then LazyFunc bind.
                bound_ctx.let_def_overlay = bound_ctx
                    .let_def_overlay
                    .cons(Arc::clone(&name), Arc::new(def.clone()));
                let domain_val = match eval_let_func_domain(&bound_ctx, bounds, span) {
                    Ok(v) => v,
                    Err(e) => return Some(Err(e)),
                };
                if !domain_val.is_set() {
                    return Some(Err(EvalError::type_error(
                        "Set",
                        &domain_val,
                        Some(def.body.span),
                    )));
                }
                let lazy = build_lazy_func_from_ctx(
                    &bound_ctx,
                    Some(Arc::clone(&name)),
                    LazyDomain::General(Box::new(domain_val)),
                    bounds,
                    *func_body.clone(),
                );
                bound_ctx = bound_ctx.into_bind_local(name, Value::LazyFunc(Arc::new(lazy)));
                continue;
            }
        }
        match eval_zero_arg_let_body(&bound_ctx, &def.body) {
            Ok(val) => bound_ctx = bound_ctx.into_bind_local(def.name.node.clone(), val),
            Err(_) => return None,
        }
    }
    Some(eval(&bound_ctx, body))
}
