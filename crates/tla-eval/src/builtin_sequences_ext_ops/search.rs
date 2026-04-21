// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{check_arity, eval, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value};
use crate::value::intern_string;
use tla_core::name_intern::{intern_name, NameId};

#[derive(Clone, Copy)]
enum MatchSelection {
    First,
    Last,
}

fn eval_select_seq_index(
    ctx: &EvalCtx,
    seq: &[Value],
    param_name: Arc<str>,
    param_id: NameId,
    body: &Spanned<Expr>,
    bool_span: Option<Span>,
    selection: MatchSelection,
) -> EvalResult<i64> {
    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();
    let mut first_iter = true;
    let mut matched_index = 0i64;

    for (i, elem) in seq.iter().enumerate() {
        if first_iter {
            local_ctx.push_binding_preinterned(Arc::clone(&param_name), elem.clone(), param_id);
            first_iter = false;
        } else {
            local_ctx.update_last_binding_value(elem.clone());
        }

        let result = eval(&local_ctx, body)?;
        let passed = result
            .as_bool()
            .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, bool_span))?;
        if passed {
            matched_index = (i as i64) + 1;
            if matches!(selection, MatchSelection::First) {
                break;
            }
        }
    }

    local_ctx.pop_to_mark(&mark);
    Ok(matched_index)
}

pub(super) fn eval_search_ops(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "SelectInSeq" => {
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;

            let test_name = match &args[1].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "SelectInSeq requires operator name as second argument".into(),
                        span,
                    });
                }
            };

            let test_def = ctx
                .get_op(&test_name)
                .ok_or_else(|| EvalError::UndefinedOp {
                    name: test_name.clone(),
                    span,
                })?;

            if test_def.params.len() != 1 {
                return Err(EvalError::ArityMismatch {
                    op: test_name,
                    expected: 1,
                    got: test_def.params.len(),
                    span,
                });
            }

            let param_name = intern_string(test_def.params[0].name.node.as_str());
            let param_id = intern_name(param_name.as_ref());
            let selected = eval_select_seq_index(
                ctx,
                seq.as_ref(),
                param_name,
                param_id,
                &test_def.body,
                Some(test_def.body.span),
                MatchSelection::First,
            )?;
            Ok(Some(Value::SmallInt(selected)))
        }

        "SelectLastInSeq" => {
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;

            let test_name = match &args[1].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "SelectLastInSeq requires operator name as second argument".into(),
                        span,
                    });
                }
            };

            let test_def = ctx
                .get_op(&test_name)
                .ok_or_else(|| EvalError::UndefinedOp {
                    name: test_name.clone(),
                    span,
                })?;

            if test_def.params.len() != 1 {
                return Err(EvalError::ArityMismatch {
                    op: test_name,
                    expected: 1,
                    got: test_def.params.len(),
                    span,
                });
            }

            let param_name = intern_string(test_def.params[0].name.node.as_str());
            let param_id = intern_name(param_name.as_ref());
            let selected = eval_select_seq_index(
                ctx,
                seq.as_ref(),
                param_name,
                param_id,
                &test_def.body,
                Some(test_def.body.span),
                MatchSelection::Last,
            )?;
            Ok(Some(Value::SmallInt(selected)))
        }

        _ => Ok(None),
    }
}
