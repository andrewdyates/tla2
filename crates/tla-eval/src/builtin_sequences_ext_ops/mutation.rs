// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{check_arity, eval, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value};
use num_traits::ToPrimitive;

pub(super) fn eval_mutation_ops(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "InsertAt" => {
            // InsertAt(s, i, e) - insert e at position i (1-indexed)
            check_arity(name, args, 3, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let iv = eval(ctx, &args[1])?;
            let i = iv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &iv, Some(args[1].span)))?
                .to_i64()
                .unwrap_or(0);
            let elem = eval(ctx, &args[2])?;

            if i < 1 || i > (seq.len() as i64 + 1) {
                return Err(EvalError::IndexOutOfBounds {
                    index: i,
                    len: seq.len(),
                    value_display: None,
                    span,
                });
            }
            let idx = (i - 1) as usize;
            let mut new_seq: Vec<Value> = seq.to_vec();
            new_seq.insert(idx, elem);
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        "RemoveAt" => {
            // RemoveAt(s, i) - remove element at position i (1-indexed)
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let iv = eval(ctx, &args[1])?;
            let i = iv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &iv, Some(args[1].span)))?
                .to_i64()
                .unwrap_or(0);

            if i < 1 || i > seq.len() as i64 {
                return Err(EvalError::IndexOutOfBounds {
                    index: i,
                    len: seq.len(),
                    value_display: None,
                    span,
                });
            }
            let idx = (i - 1) as usize;
            let mut new_seq: Vec<Value> = seq.to_vec();
            new_seq.remove(idx);
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        "ReplaceAt" => {
            // ReplaceAt(s, i, e) - replace element at position i with e (1-indexed)
            check_arity(name, args, 3, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let iv = eval(ctx, &args[1])?;
            let i = iv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &iv, Some(args[1].span)))?
                .to_i64()
                .unwrap_or(0);
            let elem = eval(ctx, &args[2])?;

            if i < 1 || i > seq.len() as i64 {
                return Err(EvalError::IndexOutOfBounds {
                    index: i,
                    len: seq.len(),
                    value_display: None,
                    span,
                });
            }
            let idx = (i - 1) as usize;
            let mut new_seq: Vec<Value> = seq.to_vec();
            new_seq[idx] = elem;
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        "Remove" => {
            // Remove(s, e) - remove first occurrence of e from sequence s
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let elem = eval(ctx, &args[1])?;

            let mut new_seq: Vec<Value> = seq.to_vec();
            if let Some(pos) = new_seq.iter().position(|x| x == &elem) {
                new_seq.remove(pos);
            }
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        "ReplaceAll" => {
            // ReplaceAll(s, old, new) - replace all occurrences of old with new in sequence s
            check_arity(name, args, 3, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let old_elem = eval(ctx, &args[1])?;
            let new_elem = eval(ctx, &args[2])?;

            let new_seq: Vec<Value> = seq
                .iter()
                .map(|x| {
                    if x == &old_elem {
                        new_elem.clone()
                    } else {
                        x.clone()
                    }
                })
                .collect();
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        _ => Ok(None),
    }
}
