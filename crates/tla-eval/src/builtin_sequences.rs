// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{
    check_arity, eval, EvalCtx, EvalError, EvalResult, Expr, SeqSetValue, Span, Spanned, Value,
};
use crate::value::{intern_string, tlc_string_len, tlc_string_subseq_utf16_offsets};
use tla_core::name_intern::{intern_name, NameId};
// Built-in Sequences module operators (Len, Head, Tail, Append, SubSeq, Seq, \o, SelectSeq)

fn eval_select_seq_filter(
    ctx: &EvalCtx,
    seq: &[Value],
    param_name: Arc<str>,
    param_id: NameId,
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Vec<Value>> {
    let mut result = Vec::with_capacity(seq.len());
    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();
    let mut first_iter = true;

    for elem in seq {
        if first_iter {
            local_ctx.push_binding_preinterned(Arc::clone(&param_name), elem.clone(), param_id);
            first_iter = false;
        } else {
            local_ctx.update_last_binding_value(elem.clone());
        }

        let test_result = eval(&local_ctx, body)?;
        let passed = test_result
            .as_bool()
            .ok_or_else(|| EvalError::type_error("BOOLEAN", &test_result, span))?;
        if passed {
            result.push(elem.clone());
        }
    }

    local_ctx.pop_to_mark(&mark);
    Ok(result)
}

pub(super) fn eval_builtin_sequences(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === Sequences ===
        "Len" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            match &sv {
                Value::Seq(s) => Ok(Some(Value::int(s.len() as i64))),
                Value::Tuple(s) => Ok(Some(Value::int(s.len() as i64))),
                Value::String(s) => Ok(Some(Value::int(tlc_string_len(s.as_ref()) as i64))),
                Value::IntFunc(f) => {
                    if tla_value::IntIntervalFunc::min(f) == 1 {
                        Ok(Some(Value::int(f.len() as i64)))
                    } else {
                        Err(EvalError::one_argument_error(
                            "Len",
                            "sequence",
                            &sv,
                            Some(args[0].span),
                        ))
                    }
                }
                Value::Func(f) => {
                    // In TLA+, sequences are functions with domain 1..n.
                    // Only accept functions whose domain is exactly {1, 2, ..., n} (or empty).
                    let mut expected: i64 = 1;
                    for key in f.domain_iter() {
                        let Some(k) = key.as_i64() else {
                            return Err(EvalError::one_argument_error(
                                "Len",
                                "sequence",
                                &sv,
                                Some(args[0].span),
                            ));
                        };
                        if k != expected {
                            return Err(EvalError::one_argument_error(
                                "Len",
                                "sequence",
                                &sv,
                                Some(args[0].span),
                            ));
                        }
                        expected += 1;
                    }
                    Ok(Some(Value::int(expected - 1)))
                }
                _ => Err(EvalError::one_argument_error(
                    "Len",
                    "sequence",
                    &sv,
                    Some(args[0].span),
                )),
            }
        }

        "Head" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // Also accept Func/IntFunc — intern table can substitute variants (#1700)
            let seq = sv
                .as_seq()
                .or_else(|| sv.to_tuple_like_elements())
                .ok_or_else(|| {
                    EvalError::one_argument_error("Head", "sequence", &sv, Some(args[0].span))
                })?;
            Ok(Some(
                seq.first()
                    .cloned()
                    .ok_or(EvalError::ApplyEmptySeq { op: "Head", span })?,
            ))
        }

        "Tail" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // Fast path: use O(log n) tail for SeqValue
            if let Some(seq_value) = sv.as_seq_value() {
                if seq_value.is_empty() {
                    return Err(EvalError::ApplyEmptySeq { op: "Tail", span });
                }
                return Ok(Some(Value::Seq(Arc::new(seq_value.tail()))));
            }
            // Fallback: also accept Func/IntFunc — intern table substitution (#1700)
            let seq = sv
                .as_seq()
                .or_else(|| sv.to_tuple_like_elements())
                .ok_or_else(|| {
                    EvalError::one_argument_error("Tail", "sequence", &sv, Some(args[0].span))
                })?;
            if seq.is_empty() {
                return Err(EvalError::ApplyEmptySeq { op: "Tail", span });
            }
            Ok(Some(Value::Seq(Arc::new(seq[1..].to_vec().into()))))
        }

        "Append" => {
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let elem = eval(ctx, &args[1])?;
            if let Some(seq_value) = sv.as_seq_value() {
                return Ok(Some(Value::Seq(Arc::new(seq_value.append(elem)))));
            }
            // Also accept Func/IntFunc — intern table can substitute variants (#1700)
            if let Some(s) = sv.as_seq().or_else(|| sv.to_tuple_like_elements()) {
                let mut v = s.to_vec();
                v.push(elem);
                Ok(Some(Value::Seq(Arc::new(v.into()))))
            } else {
                Err(EvalError::evaluating_error(
                    "Append(s, v)",
                    "sequence",
                    &sv,
                    Some(args[0].span),
                ))
            }
        }

        "SubSeq" => {
            check_arity(name, args, 3, span)?;
            let sv = eval(ctx, &args[0])?;
            let mv = eval(ctx, &args[1])?;
            let nv = eval(ctx, &args[2])?;
            let m = mv.as_i64().ok_or_else(|| {
                EvalError::argument_error(
                    "second",
                    "SubSeq",
                    "natural number",
                    &mv,
                    Some(args[1].span),
                )
            })?;
            let n = nv.as_i64().ok_or_else(|| {
                EvalError::argument_error(
                    "third",
                    "SubSeq",
                    "natural number",
                    &nv,
                    Some(args[2].span),
                )
            })?;

            match &sv {
                Value::String(s) => {
                    // TLC: if m > n, return empty string even when indices are out of range.
                    if m > n {
                        return Ok(Some(Value::String(intern_string(""))));
                    }

                    let len = tlc_string_len(s.as_ref());
                    if m < 1 || (m as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: m,
                            len,
                            value_display: None,
                            span: Some(args[1].span),
                        });
                    }
                    if n < 1 || (n as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: n,
                            len,
                            value_display: None,
                            span: Some(args[2].span),
                        });
                    }

                    let start_off = (m - 1) as usize;
                    let end_off = n as usize;
                    let substr = tlc_string_subseq_utf16_offsets(s.as_ref(), start_off..end_off);
                    Ok(Some(Value::String(intern_string(substr.as_ref()))))
                }
                Value::Seq(seq_value) => {
                    // Fast path: use O(log n) subseq for SeqValue
                    if m > n {
                        return Ok(Some(Value::Seq(Arc::new(Vec::new().into()))));
                    }
                    let len = seq_value.len();
                    if m < 1 || (m as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: m,
                            len,
                            value_display: None,
                            span: Some(args[1].span),
                        });
                    }
                    if n < 1 || (n as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: n,
                            len,
                            value_display: None,
                            span: Some(args[2].span),
                        });
                    }
                    let start = (m - 1) as usize;
                    let end = n as usize;
                    Ok(Some(Value::Seq(Arc::new(seq_value.subseq(start, end)))))
                }
                Value::Tuple(seq) => {
                    if m > n {
                        return Ok(Some(Value::Seq(Arc::new(Vec::new().into()))));
                    }
                    let len = seq.len();
                    if m < 1 || (m as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: m,
                            len,
                            value_display: None,
                            span: Some(args[1].span),
                        });
                    }
                    if n < 1 || (n as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: n,
                            len,
                            value_display: None,
                            span: Some(args[2].span),
                        });
                    }
                    let start = (m - 1) as usize;
                    let end = n as usize;
                    Ok(Some(Value::Seq(Arc::new(seq[start..end].to_vec().into()))))
                }
                Value::IntFunc(f) if tla_value::IntIntervalFunc::min(f) == 1 => {
                    if m > n {
                        return Ok(Some(Value::Seq(Arc::new(Vec::new().into()))));
                    }
                    let len = f.len();
                    if m < 1 || (m as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: m,
                            len,
                            value_display: None,
                            span: Some(args[1].span),
                        });
                    }
                    if n < 1 || (n as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: n,
                            len,
                            value_display: None,
                            span: Some(args[2].span),
                        });
                    }
                    let start = (m - 1) as usize;
                    let end = n as usize;
                    Ok(Some(Value::Seq(Arc::new(
                        f.values()[start..end].to_vec().into(),
                    ))))
                }
                Value::Func(f) => {
                    // In TLA+, sequences are functions with domain 1..n. Accept such functions here.
                    let mut expected: i64 = 1;
                    for key in f.domain_iter() {
                        if key.as_i64().unwrap_or(0) != expected {
                            return Err(EvalError::argument_error(
                                "first",
                                "SubSeq",
                                "sequence",
                                &sv,
                                Some(args[0].span),
                            ));
                        }
                        expected += 1;
                    }
                    let len = (expected - 1) as usize;
                    if m > n {
                        return Ok(Some(Value::Seq(Arc::new(Vec::new().into()))));
                    }
                    if m < 1 || (m as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: m,
                            len,
                            value_display: None,
                            span: Some(args[1].span),
                        });
                    }
                    if n < 1 || (n as usize) > len {
                        return Err(EvalError::IndexOutOfBounds {
                            index: n,
                            len,
                            value_display: None,
                            span: Some(args[2].span),
                        });
                    }

                    let mut out = Vec::with_capacity((n - m + 1) as usize);
                    for i in m..=n {
                        let key = Value::SmallInt(i);
                        let Some(v) = f.apply(&key) else {
                            return Err(EvalError::Internal {
                                message: format!(
                                    "SubSeq: function domain includes {i} but mapping has no value",
                                ),
                                span,
                            });
                        };
                        out.push(v.clone());
                    }
                    Ok(Some(Value::Seq(Arc::new(out.into()))))
                }
                _ => Err(EvalError::argument_error(
                    "first",
                    "SubSeq",
                    "sequence",
                    &sv,
                    Some(args[0].span),
                )),
            }
        }

        "Seq" => {
            check_arity(name, args, 1, span)?;
            // Seq(S) is the set of all finite sequences over S - infinite in general
            let base = eval(ctx, &args[0])?;
            Ok(Some(Value::SeqSet(SeqSetValue::new(base))))
        }

        // Sequence concatenation
        // TLC parity: StringValue \o StringValue → string concatenation
        // (Sequences.java:147-158)
        "\\o" | "\\circ" => {
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let sv2 = eval(ctx, &args[1])?;
            // String concatenation: "abc" \o "def" = "abcdef"
            if let Value::String(s1) = &sv1 {
                if let Value::String(s2) = &sv2 {
                    // Part of #3287: Route through intern_string() so the TLC
                    // string token is assigned at creation time, not at first
                    // comparison via tlc_cmp().
                    return Ok(Some(Value::String(intern_string(&format!(
                        "{}{}",
                        &**s1, &**s2
                    )))));
                }
                return Err(EvalError::evaluating_error(
                    "t \\o s",
                    "string",
                    &sv2,
                    Some(args[1].span),
                ));
            }
            // Also accept Func/IntFunc — intern table can substitute variants (#1700)
            let s1 = sv1
                .as_seq()
                .or_else(|| sv1.to_tuple_like_elements())
                .ok_or_else(|| {
                    EvalError::evaluating_error("s \\o t", "sequence", &sv1, Some(args[0].span))
                })?;
            let s2 = sv2
                .as_seq()
                .or_else(|| sv2.to_tuple_like_elements())
                .ok_or_else(|| {
                    EvalError::evaluating_error("t \\o s", "sequence", &sv2, Some(args[1].span))
                })?;
            let mut result: Vec<Value> = Vec::with_capacity(s1.len() + s2.len());
            result.extend(s1.iter().cloned());
            result.extend(s2.iter().cloned());
            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        "SelectSeq" => {
            // SelectSeq(s, Test) - filter sequence by a test operator
            // Test can be either:
            // - An operator name (Ident)
            // - An inline lambda expression (Lambda)
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            // Also accept Func/IntFunc — intern table can substitute variants (#1700)
            let seq = sv
                .as_seq()
                .or_else(|| sv.to_tuple_like_elements())
                .ok_or_else(|| {
                    EvalError::argument_error(
                        "first",
                        "SelectSeq",
                        "sequence",
                        &sv,
                        Some(args[0].span),
                    )
                })?;

            // Handle both named operator and inline lambda
            let result = match &args[1].node {
                Expr::Ident(test_name, _) => {
                    // Named operator: SelectSeq(s, OpName)
                    let test_def = ctx
                        .get_op(test_name)
                        .ok_or_else(|| EvalError::UndefinedOp {
                            name: test_name.clone(),
                            span,
                        })?;

                    if test_def.params.len() != 1 {
                        return Err(EvalError::ArityMismatch {
                            op: test_name.clone(),
                            expected: 1,
                            got: test_def.params.len(),
                            span,
                        });
                    }

                    // Pre-intern param name once — avoids per-element intern_name() calls.
                    // Part of #3032: TLC iterates directly without per-element Context creation.
                    let param_str = intern_string(test_def.params[0].name.node.as_str());
                    let param_id = intern_name(param_str.as_ref());
                    eval_select_seq_filter(
                        ctx,
                        seq.as_ref(),
                        param_str,
                        param_id,
                        &test_def.body,
                        span,
                    )?
                }
                Expr::Lambda(params, body) => {
                    // Inline lambda: SelectSeq(s, LAMBDA x: P(x))
                    if params.len() != 1 {
                        return Err(EvalError::ArityMismatch {
                            op: "SelectSeq lambda".to_string(),
                            expected: 1,
                            got: params.len(),
                            span,
                        });
                    }

                    // Pre-intern lambda param — same optimization as named operator path.
                    let param_str = intern_string(params[0].node.as_str());
                    let param_id = intern_name(param_str.as_ref());
                    eval_select_seq_filter(ctx, seq.as_ref(), param_str, param_id, body, span)?
                }
                _ => {
                    return Err(EvalError::Internal {
                        message: "SelectSeq requires an operator name or lambda as second argument"
                            .into(),
                        span,
                    });
                }
            };
            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
