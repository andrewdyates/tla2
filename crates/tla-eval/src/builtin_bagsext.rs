// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    check_arity, eval, EvalCtx, EvalError, EvalResult, Expr, FuncValue, Span, Spanned, Value,
};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::sync::Arc;

// BagsExt module operators — BagAdd, BagRemove, BagRemoveAll, FoldBag, SumBag, ProductBag

pub(super) fn eval_builtin_bagsext(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "BagAdd" => {
            // BagAdd(B, e) - add 1 to count of e in bag B
            check_arity(name, args, 2, span)?;
            let bv = eval(ctx, &args[0])?;
            let ev = eval(ctx, &args[1])?;
            // Use to_func_coerced to accept Seq/IntFunc/Tuple — intern table substitution (#1713)
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;

            // Copy entries and update/add the element count
            let mut entries: Vec<(Value, Value)> = func
                .iter()
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect();
            let mut found = false;
            for entry in &mut entries {
                if entry.0 == ev {
                    let n = entry
                        .1
                        .to_bigint()
                        .ok_or_else(|| EvalError::type_error("Int", &entry.1, span))?;
                    entry.1 = Value::big_int(n + BigInt::one());
                    found = true;
                    break;
                }
            }
            if !found {
                entries.push((ev, Value::SmallInt(1)));
                entries.sort_by(|a, b| a.0.cmp(&b.0));
            }
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        "BagRemove" => {
            // BagRemove(B, e) - remove 1 from count of e in bag B
            check_arity(name, args, 2, span)?;
            let bv = eval(ctx, &args[0])?;
            let ev = eval(ctx, &args[1])?;
            // Use to_func_coerced to accept Seq/IntFunc/Tuple — intern table substitution (#1713)
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;

            // Copy entries and update/remove the element count
            let mut entries: Vec<(Value, Value)> = Vec::new();
            for (key, val) in func.mapping_iter() {
                if *key == ev {
                    let n = val
                        .to_bigint()
                        .ok_or_else(|| EvalError::type_error("Int", val, span))?;
                    let new_count = n - BigInt::one();
                    if new_count > BigInt::zero() {
                        entries.push((key.clone(), Value::big_int(new_count)));
                    }
                    // else: drop this entry (count becomes 0 or negative)
                } else {
                    entries.push((key.clone(), val.clone()));
                }
            }
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        "BagRemoveAll" => {
            // BagRemoveAll(B, e) - completely remove e from bag B
            check_arity(name, args, 2, span)?;
            let bv = eval(ctx, &args[0])?;
            let ev = eval(ctx, &args[1])?;
            // Use to_func_coerced to accept Seq/IntFunc/Tuple — intern table substitution (#1713)
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;

            // Copy entries excluding the element
            let entries: Vec<(Value, Value)> = func
                .mapping_iter()
                .filter(|(k, _)| *k != &ev)
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        "FoldBag" => {
            // FoldBag(op, base, B) - fold a binary operator over all elements in a bag
            // Each element e with count n appears n times in the fold
            check_arity(name, args, 3, span)?;

            // Get the operator name from the first argument
            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldBag requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let base = eval(ctx, &args[1])?;
            let bv = eval(ctx, &args[2])?;
            // Use to_func_coerced to accept Seq/IntFunc/Tuple — intern table substitution (#1713)
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[2].span)))?;

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

            // Fold over the bag elements (each element appears count times)
            let mut result = base;
            for (elem, count_val) in func.mapping_iter() {
                let count = count_val
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", count_val, span))?
                    .to_i64()
                    .unwrap_or(0);
                // Apply the operator count times for this element
                for _ in 0..count {
                    let new_ctx = ctx.bind2(
                        op_def.params[0].name.node.as_str(),
                        result,
                        op_def.params[1].name.node.as_str(),
                        elem.clone(),
                    );
                    result = eval(&new_ctx, &op_def.body)?;
                }
            }

            Ok(Some(result))
        }

        "SumBag" => {
            // SumBag(B) - sum of element * count for each element in bag
            // SumBag([1 |-> 2, 3 |-> 1]) = 1*2 + 3*1 = 5
            check_arity(name, args, 1, span)?;
            let bv = eval(ctx, &args[0])?;
            // Use to_func_coerced to accept Seq/IntFunc/Tuple — intern table substitution (#1713)
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;

            let mut sum = BigInt::zero();
            for (elem, count_val) in func.mapping_iter() {
                let elem_int = elem
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", elem, span))?;
                let count = count_val
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", count_val, span))?;
                sum += elem_int * count;
            }
            Ok(Some(Value::big_int(sum)))
        }

        "ProductBag" => {
            // ProductBag(B) - product of element^count for each element in bag
            // ProductBag([2 |-> 3, 3 |-> 2]) = 2^3 * 3^2 = 8 * 9 = 72
            check_arity(name, args, 1, span)?;
            let bv = eval(ctx, &args[0])?;
            // Use to_func_coerced to accept Seq/IntFunc/Tuple — intern table substitution (#1713)
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;

            let mut product = BigInt::one();
            for (elem, count_val) in func.mapping_iter() {
                let elem_int = elem
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", elem, span))?;
                let count = count_val
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", count_val, span))?
                    .to_i64()
                    .unwrap_or(0);
                // Multiply product by elem^count
                for _ in 0..count {
                    product *= &elem_int;
                }
            }
            Ok(Some(Value::big_int(product)))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
