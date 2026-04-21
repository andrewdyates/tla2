// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR dispatch helpers for function-like and operator-like expressions.

use super::dispatch::eval_tir;
use super::StoredTirBody;
use crate::core::EvalCtx;
use crate::helpers::function_values::{
    apply_func_value_eager, apply_resolved_except_spec, ResolvedExceptPathElement,
    TirLazyExceptHandler,
};
use crate::{apply_closure_with_values, apply_user_op_with_values, eval_domain_value};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Span, Spanned};
use tla_tir::nodes::{TirExceptPathElement, TirExceptSpec, TirExpr, TirOperatorRef};
use tla_value::error::{EvalError, EvalResult};
use tla_value::{FuncSetValue, Value};

pub(super) fn eval_tir_except_at(ctx: &EvalCtx, span: Option<tla_core::Span>) -> EvalResult<Value> {
    ctx.lookup("@").ok_or_else(|| EvalError::Internal {
        message: "TIR eval: EXCEPT @ used outside an EXCEPT update".to_string(),
        span,
    })
}

pub(super) fn eval_tir_op_ref(
    ctx: &EvalCtx,
    name: &str,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let body_span = span.unwrap_or_else(Span::dummy);
    let closure = ctx.create_closure(
        vec!["x".to_string(), "y".to_string()],
        Spanned {
            node: Expr::OpRef(name.to_string()),
            span: body_span,
        },
        ctx.local_ops().clone(),
    );
    Ok(Value::Closure(Arc::new(closure)))
}

pub(super) fn eval_tir_apply(
    ctx: &EvalCtx,
    op: &Spanned<TirExpr>,
    args: &[Spanned<TirExpr>],
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if let TirExpr::Name(name_ref) = &op.node {
        if let Some(result) = try_apply_direct_tir_user_op(ctx, &name_ref.name, args, span) {
            return result;
        }
    }

    let callable = eval_tir(ctx, op)?;
    let arg_values = args
        .iter()
        .map(|arg| eval_tir(ctx, arg))
        .collect::<EvalResult<Vec<_>>>()?;
    match &callable {
        Value::Closure(closure) => {
            apply_closure_with_values(ctx, closure.as_ref(), &arg_values, span)
        }
        other => Err(EvalError::type_error("Closure", other, Some(op.span))),
    }
}

fn try_apply_direct_tir_user_op(
    ctx: &EvalCtx,
    operator_name: &str,
    args: &[Spanned<TirExpr>],
    span: Option<tla_core::Span>,
) -> Option<EvalResult<Value>> {
    if args.is_empty() {
        return None;
    }

    let resolved_name = ctx.resolve_op_name(operator_name);
    let def = ctx.get_op(resolved_name)?;
    if def.is_recursive
        || def.has_primed_param
        || crate::should_prefer_builtin_override(resolved_name, def.as_ref(), args.len(), ctx)
    {
        return None;
    }

    let arg_values = args
        .iter()
        .map(|arg| eval_tir(ctx, arg))
        .collect::<EvalResult<Vec<_>>>();
    Some(
        arg_values
            .and_then(|values| apply_user_op_with_values(ctx, resolved_name, def, &values, span)),
    )
}

pub(super) fn eval_tir_func_apply(
    ctx: &EvalCtx,
    func: &Spanned<TirExpr>,
    arg: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let func_value = eval_tir(ctx, func)?;
    let arg_value = eval_tir(ctx, arg)?;
    apply_resolved_tir_func_value(&func_value, arg_value, arg.span, span, Some(func.span))
}

pub(super) fn eval_tir_func_set(
    ctx: &EvalCtx,
    domain: &Spanned<TirExpr>,
    range: &Spanned<TirExpr>,
) -> EvalResult<Value> {
    let domain_value = eval_tir(ctx, domain)?;
    let range_value = eval_tir(ctx, range)?;
    if !domain_value.is_set() {
        return Err(EvalError::type_error(
            "Set",
            &domain_value,
            Some(domain.span),
        ));
    }
    if !range_value.is_set() {
        return Err(EvalError::type_error("Set", &range_value, Some(range.span)));
    }
    Ok(Value::FuncSet(FuncSetValue::new(domain_value, range_value)))
}

pub(super) fn eval_tir_domain(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    _span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let value = eval_tir(ctx, inner)?;
    eval_domain_value(&value).map_err(|err| match err {
        EvalError::TypeError { .. } => {
            EvalError::type_error("Function/Seq/Tuple/Record", &value, Some(inner.span))
        }
        other => other,
    })
}

pub(super) fn eval_tir_except(
    ctx: &EvalCtx,
    base: &Spanned<TirExpr>,
    specs: &[TirExceptSpec],
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let mut result = eval_tir(ctx, base)?;
    for spec in specs {
        result = apply_tir_except_spec(ctx, result, &spec.path, &spec.value, span)?;
    }
    Ok(result)
}

/// Part of #3251: delegates eager value types to shared dispatch, handles
/// LazyFunc (memoized-only) and type errors locally.
fn apply_resolved_tir_func_value(
    func_value: &Value,
    arg: Value,
    arg_span: tla_core::Span,
    span: Option<tla_core::Span>,
    func_type_span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if let Some(result) = apply_func_value_eager(func_value, &arg, Some(arg_span), span) {
        return result;
    }
    match func_value {
        Value::LazyFunc(lazy) => {
            if !lazy.in_domain(&arg) {
                return Err(EvalError::NotInDomain {
                    arg: format!("{arg}"),
                    func_display: Some(format!("{func_value}")),
                    span,
                });
            }
            if let Some(value) = lazy.memoized_value(&arg) {
                return Ok(value);
            }
            Err(EvalError::Internal {
                message: "TIR eval: LazyFunc application is not yet supported".to_string(),
                span,
            })
        }
        _ => Err(EvalError::type_error(
            "Function/Seq/Record",
            func_value,
            func_type_span,
        )),
    }
}

/// Part of #3251: pre-resolve TIR path elements and delegate to the shared
/// `apply_resolved_except_spec` with a TIR-specific lazy handler.
fn apply_tir_except_spec(
    ctx: &EvalCtx,
    value: Value,
    path: &[TirExceptPathElement],
    new_value_expr: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let resolved = path
        .iter()
        .map(|p| match p {
            TirExceptPathElement::Index(expr) => {
                Ok(ResolvedExceptPathElement::Index(eval_tir(ctx, expr)?))
            }
            TirExceptPathElement::Field(f) => Ok(ResolvedExceptPathElement::Field {
                name: f.name.clone(),
                field_id: f.field_id,
            }),
        })
        .collect::<EvalResult<Vec<_>>>()?;
    let mut eval_new = |new_ctx: &EvalCtx| eval_tir(new_ctx, new_value_expr);
    apply_resolved_except_spec(
        ctx,
        value,
        &resolved,
        &mut eval_new,
        &TirLazyExceptHandler,
        span,
    )
}

/// Evaluate a module-qualified operator reference (`M!Op(args)`).
///
/// The TIR lowerer currently inlines all module references at lowering time,
/// so this variant is never constructed. This stub resolves through the
/// existing module ref infrastructure if it is ever produced.
pub(super) fn eval_tir_operator_ref(
    ctx: &EvalCtx,
    op_ref: &TirOperatorRef,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    // If no path segments, resolve as a plain operator reference
    if op_ref.path.is_empty() {
        if op_ref.args.is_empty() {
            // Route zero-arg OperatorRef through the cached evaluation path,
            // matching the fix in dispatch/name.rs. Previously bypassed the
            // zero-arg operator cache by evaluating TIR directly.
            let resolved_name = ctx.resolve_op_name(&op_ref.operator);
            if let Some(def) = ctx.get_op(resolved_name) {
                if def.params.is_empty() {
                    let shared_scope = ctx
                        .local_ops()
                        .as_ref()
                        .and_then(|local| local.get(resolved_name))
                        .is_none()
                        && ctx
                            .shared
                            .ops
                            .get(resolved_name)
                            .is_some_and(|shared_def| Arc::ptr_eq(shared_def, def));
                    return crate::eval_ident_zero_arg::eval_resolved_zero_arg_op(
                        ctx,
                        resolved_name,
                        def,
                        span,
                        shared_scope,
                    );
                }
            }
            // Fallback for unresolved operators
            return ctx
                .eval_op(&op_ref.operator)
                .map_err(|_| EvalError::UndefinedVar {
                    name: op_ref.operator.clone(),
                    span,
                });
        }
        // Parameterized operator: evaluate args then apply
        if let Some(result) =
            try_apply_direct_tir_user_op(ctx, &op_ref.operator, &op_ref.args, span)
        {
            return result;
        }
        let arg_values = op_ref
            .args
            .iter()
            .map(|arg| eval_tir(ctx, arg))
            .collect::<EvalResult<Vec<_>>>()?;
        let resolved_name = ctx.resolve_op_name(&op_ref.operator);
        if let Some(def) = ctx.get_op(resolved_name) {
            let params = def.params.iter().map(|p| p.name.node.clone()).collect();
            let mut closure = ctx.create_closure(params, def.body.clone(), ctx.local_ops().clone());
            // Part of #3392: attach TIR body so closure application stays in TIR.
            if let Some(tir_body) = super::try_resolve_operator_tir(resolved_name) {
                closure = closure.with_tir_body(Box::new(StoredTirBody::from_arc(tir_body)));
            }
            if def.is_recursive {
                closure = closure.with_name_if_missing(Arc::from(resolved_name));
            }
            return apply_closure_with_values(ctx, &closure, &arg_values, span);
        }
        return Err(EvalError::UndefinedVar {
            name: op_ref.operator.clone(),
            span,
        });
    }

    // Module-qualified operator reference: the lowerer should have inlined this.
    // If we reach here, it means the lowerer produced an OperatorRef that wasn't
    // resolved. Report a descriptive error.
    let path_str: String = op_ref
        .path
        .iter()
        .map(|seg| seg.name.as_str())
        .collect::<Vec<_>>()
        .join("!");
    Err(EvalError::Internal {
        message: format!(
            "TIR eval: module-qualified OperatorRef '{path_str}!{}' was not inlined by the lowerer",
            op_ref.operator
        ),
        span,
    })
}

/// Evaluate a `LAMBDA x, y : body` expression.
///
/// Part of #3163: Creates a `ClosureValue` with both the AST body (for the
/// `ClosureValue` constructor) and the TIR body (for TIR-native evaluation
/// at application time). The AST body was preserved during TIR lowering.
/// When the closure is later applied, closure dispatch detects
/// the `tir_body` slot and dispatches through `eval_tir` instead of AST `eval`.
pub(super) fn eval_tir_lambda(
    ctx: &EvalCtx,
    params: &[String],
    tir_body: &Spanned<TirExpr>,
    ast_body: &tla_tir::nodes::PreservedAstBody,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let _ = span;
    let closure = ctx
        .create_closure(
            params.to_vec(),
            (*ast_body.0).clone(),
            ctx.local_ops().clone(),
        )
        .with_tir_body(Box::new(StoredTirBody::new(tir_body.clone())));
    Ok(Value::Closure(Arc::new(closure)))
}
