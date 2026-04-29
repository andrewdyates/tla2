// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! EXCEPT evaluation and lazy-function EXCEPT handlers.
//!
//! Handles `[f EXCEPT ![x] = y, ![a][b] = c, ...]` forms including
//! nested paths and lazy functions over infinite domains.

use super::super::build_lazy_func_ctx;
use super::lazy::bind_lazy_func_args;
use crate::core::EvalCtx;
use crate::helpers::eval;
use crate::value::{LazyFuncValue, Value};
use crate::MAX_RECURSION_DEPTH;
use std::sync::{Arc, LazyLock};
use tla_core::ast::{ExceptPathElement, ExceptSpec, Expr};
use tla_core::name_intern::{intern_name, NameId};
use tla_core::{Span, Spanned};
use tla_value::error::{EvalError, EvalResult};

/// Pre-interned "@" binding name and NameId for EXCEPT operations.
///
/// Part of #3895: The "@" variable is bound on every EXCEPT base case.
/// Pre-interning avoids per-operation Arc<str> allocation and intern_name
/// hash lookup in this hot path.
static EXCEPT_AT_BINDING: LazyLock<(Arc<str>, NameId)> = LazyLock::new(|| {
    let name: Arc<str> = Arc::from("@");
    let name_id = intern_name(&name);
    (name, name_id)
});

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ResolvedExceptPathElement {
    Index(Value),
    Field { name: String, field_id: NameId },
}

/// Handler for LazyFunc values in EXCEPT operations.
///
/// Part of #3251: extracted to allow AST (full lazy eval) and TIR (memoized-only)
/// paths to share the non-lazy EXCEPT dispatch in `apply_resolved_except_spec`.
pub(crate) trait LazyExceptHandler {
    fn handle_lazy_except(
        &self,
        ctx: &EvalCtx,
        func: Arc<LazyFuncValue>,
        idx: &Value,
        rest: &[ResolvedExceptPathElement],
        eval_new_value: &mut dyn FnMut(&EvalCtx) -> EvalResult<Value>,
        span: Option<Span>,
    ) -> EvalResult<Value>;
}

/// AST lazy except handler: full evaluation with depth checking.
///
/// When the LazyFunc value is not in the memo cache, this handler evaluates
/// the function body with proper recursion depth tracking. Matches TLC behavior.
pub(crate) struct AstLazyExceptHandler;

impl LazyExceptHandler for AstLazyExceptHandler {
    fn handle_lazy_except(
        &self,
        ctx: &EvalCtx,
        func: Arc<LazyFuncValue>,
        idx: &Value,
        rest: &[ResolvedExceptPathElement],
        eval_new_value: &mut dyn FnMut(&EvalCtx) -> EvalResult<Value>,
        span: Option<Span>,
    ) -> EvalResult<Value> {
        if !func.in_domain(idx) {
            return Ok(Value::LazyFunc(func));
        }
        let old_val = if let Some(v) = func.memoized_value(idx) {
            v
        } else {
            let new_depth = ctx.recursion_depth + 1;
            if new_depth > MAX_RECURSION_DEPTH {
                return Err(EvalError::Internal {
                    message: format!(
                        "Maximum recursion depth ({MAX_RECURSION_DEPTH}) exceeded in EXCEPT evaluation."
                    ),
                    span,
                });
            }
            // Part of #3423: shared binding helper for lazy-function args
            let base_ctx = build_lazy_func_ctx(ctx, &func, new_depth)?;
            let bound_ctx = bind_lazy_func_args(
                base_ctx,
                func.bounds(),
                func.pre_interned_bounds(),
                idx,
                span,
            )?;
            eval(&bound_ctx, func.body())?
        };
        let new_val = apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, self, span)?;
        let new_func = func.with_exception(idx.clone(), new_val);
        Ok(Value::LazyFunc(Arc::new(new_func)))
    }
}

/// TIR lazy except handler: memoized-only, error if not cached.
///
/// The TIR path doesn't support full lazy evaluation yet, so it requires
/// the base value to already be in the memo cache.
pub(crate) struct TirLazyExceptHandler;

impl LazyExceptHandler for TirLazyExceptHandler {
    fn handle_lazy_except(
        &self,
        ctx: &EvalCtx,
        func: Arc<LazyFuncValue>,
        idx: &Value,
        rest: &[ResolvedExceptPathElement],
        eval_new_value: &mut dyn FnMut(&EvalCtx) -> EvalResult<Value>,
        span: Option<Span>,
    ) -> EvalResult<Value> {
        if !func.in_domain(idx) {
            return Ok(Value::LazyFunc(func));
        }
        let Some(old_val) = func.memoized_value(idx) else {
            return Err(EvalError::Internal {
                message: "TIR eval: LazyFunc EXCEPT requires a memoized base value".to_string(),
                span,
            });
        };
        let new_val = apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, self, span)?;
        Ok(Value::LazyFunc(Arc::new(
            func.with_exception(idx.clone(), new_val),
        )))
    }
}

/// Evaluate [f EXCEPT ![x] = y, ![a][b] = c, ...]
pub(crate) fn eval_except(
    ctx: &EvalCtx,
    func_expr: &Spanned<Expr>,
    specs: &[ExceptSpec],
    span: Option<Span>,
) -> EvalResult<Value> {
    let fv = eval(ctx, func_expr)?;
    let mut result = fv;

    for spec in specs {
        result = apply_except_spec(ctx, result, &spec.path, &spec.value, span)?;
    }

    Ok(result)
}

fn resolve_ast_except_path_element(
    ctx: &EvalCtx,
    elem: &ExceptPathElement,
) -> EvalResult<ResolvedExceptPathElement> {
    match elem {
        ExceptPathElement::Index(idx_expr) => {
            Ok(ResolvedExceptPathElement::Index(eval(ctx, idx_expr)?))
        }
        ExceptPathElement::Field(field) => Ok(ResolvedExceptPathElement::Field {
            name: field.name.node.clone(),
            field_id: field.field_id,
        }),
    }
}

/// Apply a single EXCEPT spec to a value, supporting nested paths
/// For `![a].b = v`: first index into the function/seq at `a`, then update field `b`
pub(crate) fn apply_except_spec(
    ctx: &EvalCtx,
    value: Value,
    path: &[ExceptPathElement],
    new_value_expr: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let resolved_path = path
        .iter()
        .map(|elem| resolve_ast_except_path_element(ctx, elem))
        .collect::<EvalResult<Vec<_>>>()?;
    let mut eval_new_value = |new_ctx: &EvalCtx| eval(new_ctx, new_value_expr);
    apply_resolved_except_spec(
        ctx,
        value,
        &resolved_path,
        &mut eval_new_value,
        &AstLazyExceptHandler,
        span,
    )
}

/// Apply a single EXCEPT spec using a fully-resolved path.
///
/// Part of #3251: accepts a `lazy_handler` to allow AST and TIR paths to
/// share all non-lazy EXCEPT dispatch while providing their own LazyFunc handling.
pub(crate) fn apply_resolved_except_spec(
    ctx: &EvalCtx,
    mut value: Value,
    path: &[ResolvedExceptPathElement],
    eval_new_value: &mut dyn FnMut(&EvalCtx) -> EvalResult<Value>,
    lazy_handler: &dyn LazyExceptHandler,
    span: Option<Span>,
) -> EvalResult<Value> {
    if path.is_empty() {
        // Base case: we've navigated to the target, evaluate and return new value
        // @ refers to the old value at this position
        //
        // Part of #3895: Use clone + push_binding_preinterned with a pre-interned
        // "@" name instead of bind() which re-interns the name and allocates a
        // fresh Arc<str> on every EXCEPT operation.
        let (ref at_name, at_name_id) = *EXCEPT_AT_BINDING;
        let mut new_ctx = ctx.clone();
        new_ctx.push_binding_preinterned(Arc::clone(at_name), value, at_name_id);
        return eval_new_value(&new_ctx);
    }

    // Recursive case: navigate one level and recurse
    let (first, rest) = (&path[0], &path[1..]);

    match (&mut value, first) {
        // Function with index: f[idx]
        // Part of #3168: take/restore pattern avoids cloning inner values during
        // nested EXCEPT.
        // Part of #3964: Use Arc::get_mut (non-atomic) when refcount == 1, falling
        // back to Arc::make_mut only when the Arc is shared. In chained EXCEPT
        // operations, the intermediate value is typically uniquely owned.
        (Value::Func(f), ResolvedExceptPathElement::Index(idx)) => {
            let fm = if let Some(inner) = Arc::get_mut(f) {
                inner
            } else {
                Arc::make_mut(f)
            };
            let Some((old_val, pos, old_entry_hash, source)) = fm.take_at(idx) else {
                return Ok(value);
            };
            let new_val =
                apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, lazy_handler, span)?;
            fm.restore_at(pos, old_entry_hash, source, new_val);
            Ok(value)
        }
        // IntFunc with index
        // Part of #3964: Arc::get_mut fast path.
        (Value::IntFunc(f), ResolvedExceptPathElement::Index(idx)) => {
            let fm = if let Some(inner) = Arc::get_mut(f) {
                inner
            } else {
                Arc::make_mut(f)
            };
            let Some((old_val, pos, old_entry_hash)) = fm.take_at(idx) else {
                return Ok(value);
            };
            let new_val =
                apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, lazy_handler, span)?;
            fm.restore_at(pos, old_entry_hash, new_val);
            Ok(value)
        }
        // LazyFunc with index: delegate to handler
        (Value::LazyFunc(f), ResolvedExceptPathElement::Index(idx)) => {
            lazy_handler.handle_lazy_except(ctx, Arc::clone(f), idx, rest, eval_new_value, span)
        }
        // Record with field
        (Value::Record(r), ResolvedExceptPathElement::Field { field_id, .. }) => {
            let Some((old_val, pos, old_entry_hash)) = r.take_at_field_id(*field_id) else {
                return Ok(value);
            };
            let new_val =
                apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, lazy_handler, span)?;
            r.restore_at(pos, old_entry_hash, new_val);
            Ok(value)
        }
        // Record with index (string key)
        (Value::Record(r), ResolvedExceptPathElement::Index(idx)) => {
            let field = idx
                .as_string()
                .ok_or_else(|| EvalError::type_error("STRING", idx, span))?;
            let field_id = tla_core::intern_name(field);
            let Some((old_val, pos, old_entry_hash)) = r.take_at_field_id(field_id) else {
                return Ok(value);
            };
            let new_val =
                apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, lazy_handler, span)?;
            r.restore_at(pos, old_entry_hash, new_val);
            Ok(value)
        }
        // Sequence with index
        // Part of #3964: Arc::get_mut fast path.
        (Value::Seq(s), ResolvedExceptPathElement::Index(idx)) => {
            let i = idx
                .as_i64()
                .ok_or_else(|| EvalError::type_error("Int", idx, span))?;
            if i < 1 || i as usize > s.len() {
                return Ok(value);
            }
            let arr_idx = (i - 1) as usize;
            let sv = if let Some(inner) = Arc::get_mut(s) {
                inner
            } else {
                Arc::make_mut(s)
            };
            let Some(old_val) = sv.take_at(arr_idx) else {
                return Ok(value);
            };
            let new_val =
                apply_resolved_except_spec(ctx, old_val, rest, eval_new_value, lazy_handler, span)?;
            sv.restore_at(arr_idx, new_val);
            Ok(value)
        }
        // Tuple with index
        // Part of #3441: Use Arc::get_mut for in-place update when refcount is 1,
        // matching the COW pattern used by Func/Record/Seq EXCEPT paths.
        (Value::Tuple(t), ResolvedExceptPathElement::Index(idx)) => {
            let i = idx
                .as_i64()
                .ok_or_else(|| EvalError::type_error("Int", idx, span))?;
            if i < 1 || i as usize > t.len() {
                return Err(EvalError::IndexOutOfBounds {
                    index: i,
                    len: t.len(),
                    value_display: None,
                    span,
                });
            }
            let arr_idx = (i - 1) as usize;
            let new_val = apply_resolved_except_spec(
                ctx,
                t[arr_idx].clone(),
                rest,
                eval_new_value,
                lazy_handler,
                span,
            )?;
            if t[arr_idx] == new_val {
                return Ok(value);
            }
            if let Some(slice) = Arc::get_mut(t) {
                slice[arr_idx] = new_val;
                Ok(value)
            } else {
                let mut new_t: Vec<Value> = t.iter().cloned().collect();
                new_t[arr_idx] = new_val;
                Ok(Value::Tuple(new_t.into()))
            }
        }
        // Type mismatches
        (Value::Func(_), ResolvedExceptPathElement::Field { .. })
        | (Value::IntFunc(_), ResolvedExceptPathElement::Field { .. }) => {
            Err(EvalError::Internal {
                message: "Field access on function not supported".into(),
                span,
            })
        }
        (Value::Seq(_), ResolvedExceptPathElement::Field { .. }) => Err(EvalError::Internal {
            message: "Field access on sequence not supported".into(),
            span,
        }),
        (Value::Tuple(_), ResolvedExceptPathElement::Field { .. }) => Err(EvalError::Internal {
            message: "Field access on tuple not supported".into(),
            span,
        }),
        (v, _) => Err(EvalError::type_error("Function/Record/Seq", v, span)),
    }
}
