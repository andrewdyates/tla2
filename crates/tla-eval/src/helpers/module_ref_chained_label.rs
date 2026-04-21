// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Label selection from chained module references.
//!
//! Handles `A!B!Label` where Label is a labeled subexpression within
//! operator B of instance A, including recursive chains and
//! parameterized instances.
//!
//! Part of #3122 (subexpression label selector).

use super::super::{eval, EvalCtx, EvalError, EvalResult};
use super::module_ref_chained::resolve_chained_module_ref_operator;
use super::module_ref_label::{select_named_label, select_named_label_expr};
use super::module_ref_operator::ResolvedModuleRefOperator;
use crate::value::Value;
use tla_core::ast::{Expr, ModuleTarget};
use tla_core::{Span, Spanned};

use super::module_ref_chained::build_parameterized_target_ctx;

struct ResolvedModuleRefExpr {
    expr: Spanned<Expr>,
    eval_ctx: EvalCtx,
}

pub(super) fn try_eval_label_from_base_module_ref(
    ctx: &EvalCtx,
    base_expr: &Spanned<Expr>,
    final_op_name: &str,
    final_args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    let Some(resolved_base) = try_resolve_module_ref_expr(ctx, base_expr, span)? else {
        return Ok(None);
    };

    let Some(selected) = select_named_label_expr(&resolved_base.expr, final_op_name) else {
        return Ok(None);
    };

    if !final_args.is_empty() {
        return Err(EvalError::ArityMismatch {
            op: format!("...!{final_op_name}"),
            expected: 0,
            got: final_args.len(),
            span,
        });
    }

    Ok(Some(eval(&resolved_base.eval_ctx, &selected)?))
}

fn try_resolve_module_ref_expr(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Option<ResolvedModuleRefExpr>> {
    let Expr::ModuleRef(target, op_name, args) = &expr.node else {
        return Ok(None);
    };

    if let Some(selected) = try_resolve_module_ref_label_base(ctx, target, op_name, args, span)? {
        return Ok(Some(selected));
    }

    let Some(resolved) = try_resolve_module_ref_operator_base(ctx, target, op_name, args, span)?
    else {
        return Ok(None);
    };
    Ok(Some(ResolvedModuleRefExpr {
        expr: resolved.op_def.body.clone(),
        eval_ctx: resolved.eval_ctx,
    }))
}

fn try_resolve_module_ref_label_base(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<ResolvedModuleRefExpr>> {
    if !args.is_empty() {
        return Ok(None);
    }

    match target {
        ModuleTarget::Named(name) => Ok(ctx.get_op(name).and_then(|def| {
            select_named_label(def, op_name).map(|expr| ResolvedModuleRefExpr {
                expr,
                eval_ctx: ctx.clone(),
            })
        })),
        ModuleTarget::Parameterized(name, param_exprs) => {
            let param_ctx = build_parameterized_target_ctx(ctx, name, param_exprs)?;
            Ok(param_ctx.get_op(name).and_then(|def| {
                select_named_label(def, op_name).map(|expr| ResolvedModuleRefExpr {
                    expr,
                    eval_ctx: param_ctx.clone(),
                })
            }))
        }
        ModuleTarget::Chained(base_expr) => {
            let Some(resolved_base) = try_resolve_module_ref_expr(ctx, base_expr, span)? else {
                return Ok(None);
            };
            Ok(
                select_named_label_expr(&resolved_base.expr, op_name).map(|expr| {
                    ResolvedModuleRefExpr {
                        expr,
                        eval_ctx: resolved_base.eval_ctx,
                    }
                }),
            )
        }
    }
}

fn try_resolve_module_ref_operator_base(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<ResolvedModuleRefOperator>> {
    match target {
        ModuleTarget::Named(name) => super::module_ref_operator::try_resolve_module_ref_operator(
            ctx, name, op_name, args, span,
        ),
        ModuleTarget::Parameterized(name, param_exprs) => {
            let param_ctx = build_parameterized_target_ctx(ctx, name, param_exprs)?;
            super::module_ref_operator::try_resolve_module_ref_operator(
                &param_ctx, name, op_name, args, span,
            )
        }
        ModuleTarget::Chained(base_expr) => {
            resolve_chained_module_ref_operator(ctx, base_expr, op_name, args, span).map(Some)
        }
    }
}
