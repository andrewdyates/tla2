// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Built-in Apalache module operators.
//!
//! Provides native Rust implementations for Apalache-specific operators that
//! have placeholder bodies in `Apalache.tla`. In BFS model-checking mode:
//!
//! - `Gen(n)` generates an empty set (placeholder; symbolic generation is
//!   Apalache-specific and not applicable to explicit-state BFS).
//! - `Guess(S)` is equivalent to `CHOOSE x \in S : TRUE`.
//! - `ApaFoldSet(Op, v, S)` folds a binary operator over a set.
//! - `ApaFoldSeqLeft(Op, v, seq)` folds a binary operator left over a sequence.
//! - `Skolem(e)`, `Expand(S)`, `ConstCardinality(e)` are identity (annotation-only).
//! - `MkSeq(N, F)` builds a sequence `<<F(1), ..., F(N)>>`.
//! - `Repeat(F, N, x)` applies F(_, i) N times starting from x.

use super::{
    apply_closure_with_values, check_arity, create_closure_from_arg, eval,
    eval_iter_set_tlc_normalized, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use std::sync::Arc;

pub(super) fn eval_builtin_apalache(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // Gen(n) - Generate a symbolic value of size n.
        // In BFS mode, this is a no-op placeholder returning empty set.
        // Apalache uses this for symbolic generation which is not applicable
        // to explicit-state model checking.
        "Gen" => {
            check_arity(name, args, 1, span)?;
            // Evaluate the argument for well-formedness, but discard it.
            let nv = eval(ctx, &args[0])?;
            let _n = nv
                .as_i64()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[0].span)))?;
            // Return empty set — same as the TLA+ placeholder body `Gen(__size) == {}`.
            Ok(Some(Value::set(vec![])))
        }

        // Guess(S) - Non-deterministically pick a value from set S.
        // In BFS mode, equivalent to CHOOSE x \in S : TRUE (first in TLC order).
        "Guess" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let mut iter = eval_iter_set_tlc_normalized(ctx, &sv, Some(args[0].span))?;
            iter.next()
                .ok_or_else(|| EvalError::Internal {
                    message: "Guess requires non-empty set".into(),
                    span,
                })
                .map(Some)
        }

        // ApaFoldSet(Op, v, S) - Fold a binary operator over a set.
        // Native implementation avoids the recursive TLA+ definition.
        // Supports both named operators (Expr::Ident) and lambdas (Expr::Lambda).
        "ApaFoldSet" => {
            check_arity(name, args, 3, span)?;

            let base = eval(ctx, &args[1])?;
            let sv = eval(ctx, &args[2])?;
            let set_iter = eval_iter_set_tlc_normalized(ctx, &sv, Some(args[2].span))?;

            // Fast path: named operator — direct bind without closure overhead.
            if let Expr::Ident(op_name, _) = &args[0].node {
                if let Some(op_def) = ctx.get_op(op_name) {
                    if op_def.params.len() != 2 {
                        return Err(EvalError::ArityMismatch {
                            op: op_name.clone(),
                            expected: 2,
                            got: op_def.params.len(),
                            span,
                        });
                    }
                    let mut result = base;
                    for elem in set_iter {
                        let new_ctx = ctx.bind2(
                            op_def.params[0].name.node.as_str(),
                            result,
                            op_def.params[1].name.node.as_str(),
                            elem,
                        );
                        result = eval(&new_ctx, &op_def.body)?;
                    }
                    return Ok(Some(result));
                }
            }

            // Slow path: Lambda, closure, or stdlib builtin — use closure machinery.
            let op_value = create_closure_from_arg(ctx, &args[0], "ApaFoldSet", 2, span)?;
            let Value::Closure(ref op_closure) = op_value else {
                return Err(EvalError::Internal {
                    message: "ApaFoldSet expected an operator argument".into(),
                    span,
                });
            };
            let mut result = base;
            for elem in set_iter {
                result = apply_closure_with_values(ctx, &op_closure, &[result, elem], span)?;
            }
            Ok(Some(result))
        }

        // ApaFoldSeqLeft(Op, v, seq) - Fold a binary operator left over a sequence.
        // Native implementation avoids the recursive TLA+ definition.
        // Supports both named operators (Expr::Ident) and lambdas (Expr::Lambda).
        "ApaFoldSeqLeft" => {
            check_arity(name, args, 3, span)?;

            let base = eval(ctx, &args[1])?;
            let sv = eval(ctx, &args[2])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[2].span)))?;

            // Fast path: named operator — direct bind without closure overhead.
            if let Expr::Ident(op_name, _) = &args[0].node {
                if let Some(op_def) = ctx.get_op(op_name) {
                    if op_def.params.len() != 2 {
                        return Err(EvalError::ArityMismatch {
                            op: op_name.clone(),
                            expected: 2,
                            got: op_def.params.len(),
                            span,
                        });
                    }
                    let mut result = base;
                    for elem in seq.iter() {
                        let new_ctx = ctx.bind2(
                            op_def.params[0].name.node.as_str(),
                            result,
                            op_def.params[1].name.node.as_str(),
                            elem.clone(),
                        );
                        result = eval(&new_ctx, &op_def.body)?;
                    }
                    return Ok(Some(result));
                }
            }

            // Slow path: Lambda, closure, or stdlib builtin — use closure machinery.
            let op_value = create_closure_from_arg(ctx, &args[0], "ApaFoldSeqLeft", 2, span)?;
            let Value::Closure(ref op_closure) = op_value else {
                return Err(EvalError::Internal {
                    message: "ApaFoldSeqLeft expected an operator argument".into(),
                    span,
                });
            };
            let mut result = base;
            for elem in seq.iter() {
                result =
                    apply_closure_with_values(ctx, &op_closure, &[result, elem.clone()], span)?;
            }
            Ok(Some(result))
        }

        // Skolem(e) - Identity operator (annotation hint for Apalache).
        "Skolem" => {
            check_arity(name, args, 1, span)?;
            eval(ctx, &args[0]).map(Some)
        }

        // Expand(S) - Identity operator (annotation hint for Apalache).
        "Expand" => {
            check_arity(name, args, 1, span)?;
            eval(ctx, &args[0]).map(Some)
        }

        // ConstCardinality(e) - Identity operator (annotation hint for Apalache).
        "ConstCardinality" => {
            check_arity(name, args, 1, span)?;
            eval(ctx, &args[0]).map(Some)
        }

        // MkSeq(N, F) - Build a sequence <<F(1), ..., F(N)>>.
        // The TLA+ body is `[ __i \in (1..__N) |-> __F(__i) ]` which produces
        // a function, not a sequence. The builtin produces a proper Seq value.
        // Supports both named operators (Expr::Ident) and lambdas (Expr::Lambda).
        "MkSeq" => {
            check_arity(name, args, 2, span)?;
            let nv = eval(ctx, &args[0])?;
            let n = nv
                .as_i64()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[0].span)))?;

            if n < 0 {
                return Err(EvalError::ArgumentError {
                    position: "first",
                    op: "MkSeq".to_string(),
                    expected_type: "non-negative integer",
                    value_display: format!("{n}"),
                    span,
                });
            }

            // Fast path: named operator — direct bind without closure overhead.
            if let Expr::Ident(op_name, _) = &args[1].node {
                if let Some(op_def) = ctx.get_op(op_name) {
                    if op_def.params.len() != 1 {
                        return Err(EvalError::ArityMismatch {
                            op: op_name.clone(),
                            expected: 1,
                            got: op_def.params.len(),
                            span,
                        });
                    }
                    let mut result = Vec::with_capacity(n as usize);
                    for i in 1..=n {
                        let new_ctx = ctx.bind(op_def.params[0].name.node.as_str(), Value::int(i));
                        result.push(eval(&new_ctx, &op_def.body)?);
                    }
                    return Ok(Some(Value::Seq(Arc::new(result.into()))));
                }
            }

            // Slow path: Lambda, closure, or stdlib builtin — use closure machinery.
            let op_value = create_closure_from_arg(ctx, &args[1], "MkSeq", 1, span)?;
            let Value::Closure(ref op_closure) = op_value else {
                return Err(EvalError::Internal {
                    message: "MkSeq expected an operator argument".into(),
                    span,
                });
            };
            let mut result = Vec::with_capacity(n as usize);
            for i in 1..=n {
                result.push(apply_closure_with_values(
                    ctx,
                    &op_closure,
                    &[Value::int(i)],
                    span,
                )?);
            }
            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        // Repeat(F, N, x) - Apply F(_, i) N times starting from x.
        // Repeat(F, N, x) == IF N <= 0 THEN x ELSE F(Repeat(F, N-1, x), N)
        // Supports both named operators (Expr::Ident) and lambdas (Expr::Lambda).
        "Repeat" => {
            check_arity(name, args, 3, span)?;

            let nv = eval(ctx, &args[1])?;
            let n = nv
                .as_i64()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[1].span)))?;

            let initial = eval(ctx, &args[2])?;

            if n <= 0 {
                return Ok(Some(initial));
            }

            // Fast path: named operator — direct bind without closure overhead.
            if let Expr::Ident(op_name, _) = &args[0].node {
                if let Some(op_def) = ctx.get_op(op_name) {
                    if op_def.params.len() != 2 {
                        return Err(EvalError::ArityMismatch {
                            op: op_name.clone(),
                            expected: 2,
                            got: op_def.params.len(),
                            span,
                        });
                    }
                    // Iterative implementation (avoids deep recursion for large N):
                    // result_0 = x
                    // result_i = F(result_{i-1}, i)  for i = 1..N
                    let mut result = initial;
                    for i in 1..=n {
                        let new_ctx = ctx.bind2(
                            op_def.params[0].name.node.as_str(),
                            result,
                            op_def.params[1].name.node.as_str(),
                            Value::int(i),
                        );
                        result = eval(&new_ctx, &op_def.body)?;
                    }
                    return Ok(Some(result));
                }
            }

            // Slow path: Lambda, closure, or stdlib builtin — use closure machinery.
            let op_value = create_closure_from_arg(ctx, &args[0], "Repeat", 2, span)?;
            let Value::Closure(ref op_closure) = op_value else {
                return Err(EvalError::Internal {
                    message: "Repeat expected an operator argument".into(),
                    span,
                });
            };
            let mut result = initial;
            for i in 1..=n {
                result =
                    apply_closure_with_values(ctx, &op_closure, &[result, Value::int(i)], span)?;
            }
            Ok(Some(result))
        }

        // SetAsFun(S) - Convert a set of pairs to a function.
        // More efficient than the TLA+ CHOOSE-based definition.
        "SetAsFun" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let set_iter = eval_iter_set_tlc_normalized(ctx, &sv, Some(args[0].span))?;

            let mut entries: Vec<(Value, Value)> = Vec::new();
            for pair in set_iter {
                let tuple = pair
                    .as_seq()
                    .or_else(|| pair.to_tuple_like_elements())
                    .ok_or_else(|| {
                        EvalError::type_error("<<key, value>> pair", &pair, Some(args[0].span))
                    })?;
                if tuple.len() != 2 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "SetAsFun: expected pairs (2-tuples), got {}-tuple",
                            tuple.len()
                        ),
                        span,
                    });
                }
                entries.push((tuple[0].clone(), tuple[1].clone()));
            }
            // Sort by key for deterministic function construction
            entries.sort_by(|(a, _), (b, _)| a.cmp(b));
            // Deduplicate: last entry wins (TLC behavior with CHOOSE)
            entries.dedup_by(|(a, _), (b, _)| a == b);

            Ok(Some(Value::Func(Arc::new(
                crate::value::FuncValue::from_sorted_entries(entries),
            ))))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
