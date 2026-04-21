// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound variable binding helpers for quantifiers, function definitions, and EXCEPT.
//!
//! Extracted from `quantifiers.rs` as part of #3425 to separate reusable
//! binding/pre-intern helpers (consumed by many sibling modules) from
//! quantifier evaluation control flow.

use super::super::{EvalCtx, EvalError, EvalResult};
use crate::value::{intern_string, Value};
use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar};
use tla_core::name_intern::{intern_name, NameId};
use tla_core::Span;

/// Bind a bound variable to an element using bind_local (always adds to local_stack).
/// Takes ownership of the `EvalCtx` to avoid cloning. Use when the caller already owns
/// the context (e.g., accumulator patterns in multi-arg function application).
///
/// Issue #100: Without using bind_local, parameters bound only in env are not tracked
/// as dependencies by eval_with_dep_tracking, causing ZERO_ARG_OP_CACHE to return
/// stale values when the bound variable changes across recursive calls.
pub(crate) fn into_bind_local_bound_var(
    ctx: EvalCtx,
    bound: &BoundVar,
    elem: &Value,
    span: Option<Span>,
) -> EvalResult<EvalCtx> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(vars)) => {
            let tuple = elem
                .to_tuple_like_elements()
                .ok_or_else(|| EvalError::type_error("Tuple", elem, span))?;
            if tuple.len() != vars.len() {
                return Err(EvalError::Internal {
                    message: format!(
                        "Tuple pattern has {} variables but element has {} components",
                        vars.len(),
                        tuple.len()
                    ),
                    span,
                });
            }
            let mut new_ctx = ctx;
            for (var, val) in vars.iter().zip(tuple.iter()) {
                new_ctx = new_ctx.into_bind_local(var.node.clone(), val.clone());
            }
            Ok(new_ctx)
        }
        Some(BoundPattern::Var(var)) => Ok(ctx.into_bind_local(var.node.clone(), elem.clone())),
        None => Ok(ctx.into_bind_local(bound.name.node.clone(), elem.clone())),
    }
}

pub(crate) fn into_bind_local_bound_var_cached(
    mut ctx: EvalCtx,
    bound: &BoundVar,
    elem: &Value,
    simple: Option<(&Arc<str>, NameId)>,
    tuple: Option<&[(Arc<str>, NameId)]>,
    span: Option<Span>,
) -> EvalResult<EvalCtx> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(vars)) => {
            let values = elem
                .to_tuple_like_elements()
                .ok_or_else(|| EvalError::type_error("Tuple", elem, span))?;
            if values.len() != vars.len() {
                return Err(EvalError::Internal {
                    message: format!(
                        "Tuple pattern has {} variables but element has {} components",
                        vars.len(),
                        values.len()
                    ),
                    span,
                });
            }

            let mut new_ctx = ctx;
            if let Some(entries) = tuple {
                for ((_name, id), value) in entries.iter().zip(values.iter()) {
                    new_ctx.push_binding_by_id(*id, value.clone());
                }
            } else {
                for (var, value) in vars.iter().zip(values.iter()) {
                    new_ctx = new_ctx.into_bind_local(var.node.clone(), value.clone());
                }
            }
            Ok(new_ctx)
        }
        Some(BoundPattern::Var(var)) => {
            if let Some((_name, id)) = simple {
                ctx.push_binding_by_id(id, elem.clone());
                Ok(ctx)
            } else {
                Ok(ctx.into_bind_local(var.node.clone(), elem.clone()))
            }
        }
        None => {
            if let Some((_name, id)) = simple {
                ctx.push_binding_by_id(id, elem.clone());
                Ok(ctx)
            } else {
                Ok(ctx.into_bind_local(bound.name.node.clone(), elem.clone()))
            }
        }
    }
}

/// Pre-interned binding info for a bound variable, computed once before a quantifier loop.
/// Avoids repeated intern_string + intern_name (2 DashMap lookups) per loop iteration.
pub(crate) struct PreInternedBound {
    /// For simple (non-pattern) bindings: single pre-interned name + id.
    pub(crate) simple: Option<(Arc<str>, NameId)>,
    /// For tuple pattern bindings: pre-interned names + ids for each component.
    pub(crate) tuple: Option<Vec<(Arc<str>, NameId)>>,
}

impl PreInternedBound {
    pub(crate) fn from_bound(bound: &BoundVar) -> Self {
        match &bound.pattern {
            Some(BoundPattern::Tuple(vars)) => {
                let tuple = vars
                    .iter()
                    .map(|var| {
                        let interned = intern_string(var.node.as_str());
                        let id = intern_name(interned.as_ref());
                        (interned, id)
                    })
                    .collect();
                PreInternedBound {
                    simple: None,
                    tuple: Some(tuple),
                }
            }
            Some(BoundPattern::Var(var)) => {
                let interned = intern_string(var.node.as_str());
                let id = intern_name(interned.as_ref());
                PreInternedBound {
                    simple: Some((interned, id)),
                    tuple: None,
                }
            }
            None => {
                let interned = intern_string(bound.name.node.as_str());
                let id = intern_name(interned.as_ref());
                PreInternedBound {
                    simple: Some((interned, id)),
                    tuple: None,
                }
            }
        }
    }
}

/// Push a bound variable binding onto a mutable context's stack.
/// Use with `ctx.mark_stack()` before and `ctx.pop_to_mark(mark)` after the body evaluation.
/// This avoids allocating a new EvalCtx per element in hot loops.
pub fn push_bound_var_mut(
    ctx: &mut EvalCtx,
    bound: &BoundVar,
    elem: &Value,
    span: Option<Span>,
) -> EvalResult<()> {
    push_bound_var_mut_preinterned(ctx, bound, elem, span, None)
}

/// Push a bound variable binding, optionally using pre-interned name info.
/// When `pre` is Some, avoids intern_string/intern_name per call (hot-loop optimization).
pub(crate) fn push_bound_var_mut_preinterned(
    ctx: &mut EvalCtx,
    bound: &BoundVar,
    elem: &Value,
    span: Option<Span>,
    pre: Option<&PreInternedBound>,
) -> EvalResult<()> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(vars)) => {
            // Destructure tuple-like value and bind each variable
            // TLC-parity: accept Seq, Tuple, and sequence-like functions (domain 1..n)
            let tuple = elem
                .to_tuple_like_elements()
                .ok_or_else(|| EvalError::type_error("Tuple", elem, span))?;
            if tuple.len() != vars.len() {
                return Err(EvalError::Internal {
                    message: format!(
                        "Tuple pattern has {} variables but element has {} components",
                        vars.len(),
                        tuple.len()
                    ),
                    span,
                });
            }
            if let Some(pre) = pre.and_then(|p| p.tuple.as_ref()) {
                for ((_name, id), val) in pre.iter().zip(tuple.iter()) {
                    ctx.push_binding_by_id(*id, val.clone());
                }
            } else {
                for (var, val) in vars.iter().zip(tuple.iter()) {
                    let name: Arc<str> = Arc::from(var.node.as_str());
                    ctx.push_binding(name, val.clone());
                }
            }
            Ok(())
        }
        Some(BoundPattern::Var(_)) | None => {
            if let Some((_name, id)) = pre.and_then(|p| p.simple.as_ref()) {
                ctx.push_binding_by_id(*id, elem.clone());
            } else {
                let raw_name = match &bound.pattern {
                    Some(BoundPattern::Var(var)) => var.node.as_str(),
                    _ => bound.name.node.as_str(),
                };
                let name: Arc<str> = Arc::from(raw_name);
                ctx.push_binding(name, elem.clone());
            }
            Ok(())
        }
    }
}

/// Push a bound variable binding, taking ownership of the value (no clone).
/// Part of #3073: For simple (non-tuple) bindings, avoids the redundant clone
/// in push_bound_var_mut_preinterned by moving the value directly into the context.
/// Only for simple bindings — tuple patterns still need the borrowed variant
/// because to_tuple_like_elements returns references.
pub(crate) fn push_bound_var_owned_preinterned(
    ctx: &mut EvalCtx,
    bound: &BoundVar,
    elem: Value,
    span: Option<Span>,
    pre: Option<&PreInternedBound>,
) -> EvalResult<()> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(_)) => {
            // Fall back to borrowed path for tuple patterns.
            push_bound_var_mut_preinterned(ctx, bound, &elem, span, pre)
        }
        Some(BoundPattern::Var(_)) | None => {
            if let Some((_name, id)) = pre.and_then(|p| p.simple.as_ref()) {
                ctx.push_binding_by_id(*id, elem);
            } else {
                let raw_name = match &bound.pattern {
                    Some(BoundPattern::Var(var)) => var.node.as_str(),
                    _ => bound.name.node.as_str(),
                };
                let name: Arc<str> = Arc::from(raw_name);
                ctx.push_binding(name, elem);
            }
            Ok(())
        }
    }
}
