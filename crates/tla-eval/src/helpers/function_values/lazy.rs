// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared lazy-function binding helpers for apply and EXCEPT paths.
//!
//! Both `apply_resolved_func_value` and `AstLazyExceptHandler` need the same
//! broad sequence when evaluating a lazy function body:
//!
//! 1. check recursion depth
//! 2. call `build_lazy_func_ctx`
//! 3. bind one or more arguments using pre-interned bounds
//! 4. evaluate the lazy body
//!
//! This module extracts the shared binding step (3) so that each caller owns
//! only its mode-specific behaviour (apply adds the recursive-local rebind
//! fast path from #3395; EXCEPT does not).
//!
//! Part of #3423.

use super::super::into_bind_local_bound_var;
use crate::core::EvalCtx;
use std::sync::Arc;
use tla_core::ast::BoundPattern;
use tla_core::name_intern::NameId;
use tla_core::Span;
use tla_value::error::{EvalError, EvalResult};

use crate::value::Value;
use tla_core::ast::BoundVar;

/// Bind lazy-function arguments to the evaluation context.
///
/// For single-variable functions with a simple pattern, binds using the
/// pre-interned name directly. For multi-variable functions, decomposes
/// the argument as a tuple and binds each component.
///
/// This is the shared binding path. The apply caller may skip this for
/// single-var cases when its recursive-local rebind fast path succeeds.
pub(super) fn bind_lazy_func_args(
    base_ctx: EvalCtx,
    bounds: &[BoundVar],
    pre_interned: &[(Arc<str>, NameId)],
    arg: &Value,
    span: Option<Span>,
) -> EvalResult<EvalCtx> {
    if bounds.len() == 1 {
        bind_single_var(base_ctx, &bounds[0], &pre_interned[0], arg, span)
    } else {
        bind_multi_var(base_ctx, bounds, pre_interned, arg, span)
    }
}

/// Bind a single bound variable using the pre-interned name.
fn bind_single_var(
    base_ctx: EvalCtx,
    bound: &BoundVar,
    (_name, id): &(Arc<str>, NameId),
    arg: &Value,
    span: Option<Span>,
) -> EvalResult<EvalCtx> {
    if bound.pattern.is_none() || matches!(&bound.pattern, Some(BoundPattern::Var(_))) {
        Ok(base_ctx.into_bind_by_id(*id, arg.clone()))
    } else {
        into_bind_local_bound_var(base_ctx, bound, arg, span)
    }
}

/// Decompose a tuple argument and bind each component to its bound variable.
fn bind_multi_var(
    base_ctx: EvalCtx,
    bounds: &[BoundVar],
    pre_interned: &[(Arc<str>, NameId)],
    arg: &Value,
    span: Option<Span>,
) -> EvalResult<EvalCtx> {
    let components = arg
        .to_tuple_like_elements()
        .ok_or_else(|| EvalError::type_error("Tuple", arg, span))?;
    if components.len() != bounds.len() {
        return Err(EvalError::type_error("Tuple", arg, span));
    }
    let mut ctx = base_ctx;
    for (i, bound) in bounds.iter().enumerate() {
        if bound.pattern.is_none() || matches!(&bound.pattern, Some(BoundPattern::Var(_))) {
            let (ref _name, id) = pre_interned[i];
            ctx = ctx.into_bind_by_id(id, components[i].clone());
        } else {
            ctx = into_bind_local_bound_var(ctx, bound, &components[i], span)?;
        }
    }
    Ok(ctx)
}
