// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
// Common stdlib operators — Min, Max, STRING, Abs, Sign, Range

pub(super) fn eval_builtin_stdlib_ext(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === Other common stdlib ===
        "Min" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let min_value = eval_iter_set(ctx, &sv, Some(args[0].span))?
                .filter_map(|v| v.to_bigint())
                .min();
            min_value
                .map(Value::big_int)
                .ok_or_else(|| EvalError::Internal {
                    message: "Min requires non-empty set of integers".into(),
                    span,
                })
                .map(Some)
        }

        "Max" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let max_value = eval_iter_set(ctx, &sv, Some(args[0].span))?
                .filter_map(|v| v.to_bigint())
                .max();
            max_value
                .map(Value::big_int)
                .ok_or_else(|| EvalError::Internal {
                    message: "Max requires non-empty set of integers".into(),
                    span,
                })
                .map(Some)
        }

        // === Strings module ===

        // STRING - the set of all strings (infinite)
        "STRING" => {
            check_arity(name, args, 0, span)?;
            Ok(Some(Value::StringSet))
        }

        "Abs" => {
            // Abs(n) - absolute value of an integer
            check_arity(name, args, 1, span)?;
            let nv = eval(ctx, &args[0])?;
            // SmallInt fast path
            if let Value::SmallInt(n) = nv {
                return Ok(Some(Value::SmallInt(n.abs())));
            }
            let n = nv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[0].span)))?;
            use num_traits::Signed;
            Ok(Some(Value::big_int(n.abs())))
        }

        "Sign" => {
            // Sign(n) - returns -1, 0, or 1 based on sign of n
            check_arity(name, args, 1, span)?;
            let nv = eval(ctx, &args[0])?;
            // SmallInt fast path
            if let Value::SmallInt(n) = nv {
                return Ok(Some(Value::SmallInt(n.signum())));
            }
            let n = nv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[0].span)))?;
            use num_traits::Signed;
            let signum = n.signum();
            Ok(Some(Value::big_int(signum)))
        }

        "Range" => {
            // Range(f) - the set of all values in the function's mapping (co-domain image)
            check_arity(name, args, 1, span)?;
            let fv = eval(ctx, &args[0])?;
            let values: Vec<Value> = match &fv {
                Value::Func(func) => func.mapping_values().cloned().collect(),
                Value::IntFunc(func) => func.values().to_vec(),
                Value::Seq(seq) => seq.iter().cloned().collect(),
                Value::Tuple(seq) => seq.iter().cloned().collect(),
                _ => {
                    return Err(EvalError::type_error(
                        "Function/Seq",
                        &fv,
                        Some(args[0].span),
                    ));
                }
            };
            Ok(Some(Value::set(values)))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
