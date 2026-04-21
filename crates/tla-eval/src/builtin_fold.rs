// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    apply_binary_op, apply_builtin_binary_op, apply_closure_with_values, apply_named_binary_op,
    check_arity, create_closure_from_arg, eval, eval_iter_set_tlc_normalized, EvalCtx, EvalError,
    EvalResult, Expr, OperatorRef, Span, Spanned, Value,
};
// Fold operations — FoldLeft, FoldRight, FoldSet, FoldFunction, FoldFunctionOnSet, FoldSeq

pub(super) fn eval_builtin_fold(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "FoldLeft" => {
            // FoldLeft(Op, base, s) - fold left over sequence (alias for FoldSeq)
            check_arity(name, args, 3, span)?;

            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldLeft requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let base = eval(ctx, &args[1])?;
            let sv = eval(ctx, &args[2])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[2].span)))?;

            let op_def = ctx.get_op(&op_name).ok_or_else(|| EvalError::UndefinedOp {
                name: op_name.clone(),
                span,
            })?;

            if op_def.params.len() != 2 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
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

            Ok(Some(result))
        }

        "FoldRight" => {
            // FoldRight(Op, s, base) - fold right over sequence
            // Note: argument order is Op, s, base (unlike FoldLeft which is Op, base, s)
            check_arity(name, args, 3, span)?;

            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldRight requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let sv = eval(ctx, &args[1])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[1].span)))?;
            let base = eval(ctx, &args[2])?;

            let op_def = ctx.get_op(&op_name).ok_or_else(|| EvalError::UndefinedOp {
                name: op_name.clone(),
                span,
            })?;

            if op_def.params.len() != 2 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 2,
                    got: op_def.params.len(),
                    span,
                });
            }

            // Fold from right to left
            let mut result = base;
            for elem in seq.iter().rev() {
                let new_ctx = ctx.bind2(
                    op_def.params[0].name.node.as_str(),
                    elem.clone(),
                    op_def.params[1].name.node.as_str(),
                    result,
                );
                result = eval(&new_ctx, &op_def.body)?;
            }

            Ok(Some(result))
        }

        "FoldSet" => {
            // FoldSet(Op, base, S) - fold a binary operator over a set
            // Op is the name of a binary operator
            check_arity(name, args, 3, span)?;

            // Get the operator name from the first argument
            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldSet requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let base = eval(ctx, &args[1])?;
            let sv = eval(ctx, &args[2])?;
            // Part of #2987: use TLC-normalized order for fold iteration.
            // FoldSet with non-commutative ops produces order-dependent results.
            let set_iter = eval_iter_set_tlc_normalized(ctx, &sv, Some(args[2].span))?;

            // Get the operator definition
            let op_def = ctx.get_op(&op_name).ok_or_else(|| EvalError::UndefinedOp {
                name: op_name.clone(),
                span,
            })?;

            if op_def.params.len() != 2 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 2,
                    got: op_def.params.len(),
                    span,
                });
            }

            // Fold over the set elements
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

            Ok(Some(result))
        }

        "FoldFunction" => {
            // FoldFunction(Op, base, f) - fold a binary operator over a function's range
            // Op is a binary operator argument (name, operator parameter, lambda, or built-in OpRef).
            check_arity(name, args, 3, span)?;

            let base = eval(ctx, &args[1])?;
            let fv = eval(ctx, &args[2])?;

            // Fast path: when Op is a simple Ident or OpRef, use direct operator
            // application (ctx.bind() for user-defined, inline for stdlib builtins,
            // apply_builtin_binary_op for OpRef). This avoids the expensive closure
            // machinery (full env clone + local_stack reconstruction per fold element).
            // Falls back to closure path for lambdas and operator parameters.
            let use_fast_path = match &args[0].node {
                Expr::Ident(ident_name, _) => {
                    // Closure values in env need the closure path
                    if let Some(Value::Closure(_)) = ctx.lookup(ident_name) {
                        false
                    } else {
                        true // user-defined or stdlib builtin
                    }
                }
                Expr::OpRef(_) => true,
                _ => false, // Lambda or complex expr → closure path
            };

            if use_fast_path {
                // Fast path: direct operator application (no closure overhead)
                let mut result = base;
                // Macro-like closure to apply the op per element
                let apply_op = |left: Value, right: Value| -> EvalResult<Value> {
                    match &args[0].node {
                        Expr::Ident(ident_name, _) => {
                            apply_named_binary_op(ctx, ident_name, left, right, span)
                        }
                        Expr::OpRef(op) => apply_builtin_binary_op(op, left, right, span),
                        _ => unreachable!(
                            "builtin_fold fast path: use_fast_path guard ensures Ident|OpRef"
                        ),
                    }
                };
                match &fv {
                    Value::Func(func) => {
                        for (_key, value) in func.mapping_iter() {
                            let acc = result;
                            result = apply_op(value.clone(), acc)?;
                        }
                    }
                    Value::IntFunc(func) => {
                        for value in func.values() {
                            let acc = result;
                            result = apply_op(value.clone(), acc)?;
                        }
                    }
                    Value::Seq(seq) => {
                        for value in seq.iter() {
                            let acc = result;
                            result = apply_op(value.clone(), acc)?;
                        }
                    }
                    Value::Tuple(seq) => {
                        for value in seq.iter() {
                            let acc = result;
                            result = apply_op(value.clone(), acc)?;
                        }
                    }
                    Value::Record(rec) => {
                        for (_k, value) in rec.iter() {
                            let acc = result;
                            result = apply_op(value.clone(), acc)?;
                        }
                    }
                    _ => {
                        return Err(EvalError::type_error(
                            "Function/Seq/Tuple/Record",
                            &fv,
                            Some(args[2].span),
                        ));
                    }
                }
                Ok(Some(result))
            } else {
                // Slow path: closure machinery for lambdas and operator parameters
                let op_value = create_closure_from_arg(ctx, &args[0], "FoldFunction", 2, span)?;
                let Value::Closure(ref op_closure) = op_value else {
                    return Err(EvalError::Internal {
                        message: "FoldFunction expected an operator argument".into(),
                        span,
                    });
                };

                let mut result = base;
                match &fv {
                    Value::Func(func) => {
                        for (_key, value) in func.mapping_iter() {
                            let acc = result;
                            result = apply_closure_with_values(
                                ctx,
                                &op_closure,
                                &[value.clone(), acc],
                                span,
                            )?;
                        }
                    }
                    Value::IntFunc(func) => {
                        for value in func.values() {
                            let acc = result;
                            result = apply_closure_with_values(
                                ctx,
                                &op_closure,
                                &[value.clone(), acc],
                                span,
                            )?;
                        }
                    }
                    Value::Seq(seq) => {
                        for value in seq.iter() {
                            let acc = result;
                            result = apply_closure_with_values(
                                ctx,
                                &op_closure,
                                &[value.clone(), acc],
                                span,
                            )?;
                        }
                    }
                    Value::Tuple(seq) => {
                        for value in seq.iter() {
                            let acc = result;
                            result = apply_closure_with_values(
                                ctx,
                                &op_closure,
                                &[value.clone(), acc],
                                span,
                            )?;
                        }
                    }
                    Value::Record(rec) => {
                        for (_k, value) in rec.iter() {
                            let acc = result;
                            result = apply_closure_with_values(
                                ctx,
                                &op_closure,
                                &[value.clone(), acc],
                                span,
                            )?;
                        }
                    }
                    _ => {
                        return Err(EvalError::type_error(
                            "Function/Seq/Tuple/Record",
                            &fv,
                            Some(args[2].span),
                        ));
                    }
                }
                Ok(Some(result))
            }
        }

        "FoldFunctionOnSet" => {
            // FoldFunctionOnSet(Op, base, f, S) - fold a binary operator over a function's range
            // restricted to keys in set S
            // Op is the name of a binary operator or a built-in operator reference
            check_arity(name, args, 4, span)?;

            // Get the operator: either a user-defined operator name or a built-in operator reference
            let op_ref = match &args[0].node {
                Expr::Ident(name, _) => OperatorRef::UserDefined(name.clone()),
                Expr::OpRef(op) => OperatorRef::BuiltIn(op.clone()),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldFunctionOnSet requires operator name as first argument"
                            .into(),
                        span,
                    });
                }
            };

            let base = eval(ctx, &args[1])?;
            let fv = eval(ctx, &args[2])?;
            let sv = eval(ctx, &args[3])?;
            // Part of #2987: use TLC-normalized order for fold iteration.
            let subset: Vec<Value> =
                eval_iter_set_tlc_normalized(ctx, &sv, Some(args[3].span))?.collect();

            // Fold over the function's values for keys in S
            let mut result = base;
            match &fv {
                Value::Func(func) => {
                    for key in &subset {
                        if let Some(value) = func.mapping_get(key) {
                            result = apply_binary_op(ctx, &op_ref, value.clone(), result, span)?;
                        }
                    }
                }
                Value::IntFunc(func) => {
                    for key in &subset {
                        if let Some(value) = func.apply(key) {
                            result = apply_binary_op(ctx, &op_ref, value.clone(), result, span)?;
                        }
                    }
                }
                Value::Seq(seq) => {
                    // Sequences are functions from 1..n
                    for key in &subset {
                        if let Some(i) = key.as_i64() {
                            if i >= 1 && (i as usize) <= seq.len() {
                                let value = &seq[(i - 1) as usize];
                                result =
                                    apply_binary_op(ctx, &op_ref, value.clone(), result, span)?;
                            }
                        }
                    }
                }
                Value::Tuple(seq) => {
                    for key in &subset {
                        if let Some(i) = key.as_i64() {
                            if i >= 1 && (i as usize) <= seq.len() {
                                let value = &seq[(i - 1) as usize];
                                result =
                                    apply_binary_op(ctx, &op_ref, value.clone(), result, span)?;
                            }
                        }
                    }
                }
                _ => return Err(EvalError::type_error("Func/Seq", &fv, Some(args[2].span))),
            }

            Ok(Some(result))
        }

        "FoldSeq" => {
            // FoldSeq(Op, base, s) - fold a binary operator over a sequence (left to right)
            // Op is the name of a binary operator
            check_arity(name, args, 3, span)?;

            // Get the operator name from the first argument
            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldSeq requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let base = eval(ctx, &args[1])?;
            let sv = eval(ctx, &args[2])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[2].span)))?;

            // Get the operator definition
            let op_def = ctx.get_op(&op_name).ok_or_else(|| EvalError::UndefinedOp {
                name: op_name.clone(),
                span,
            })?;

            if op_def.params.len() != 2 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 2,
                    got: op_def.params.len(),
                    span,
                });
            }

            // Fold over the sequence elements (left to right)
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

            Ok(Some(result))
        }

        _ => Ok(None),
    }
}
