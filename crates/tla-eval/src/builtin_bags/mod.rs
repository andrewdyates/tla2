// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Built-in Bags module operators.
//
// Simple operations (EmptyBag, IsABag, SetToBag, BagToSet, BagIn, CopiesIn,
// BagCardinality, BagCup, BagDiff) are here. Complex combinatorial operations
// (BagUnion, BagOfAll, SubBag, SqSubseteq) are in `combinatorial`.

mod combinatorial;

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, FuncValue, SortedSet,
    Span, Spanned, Value,
};
use num_bigint::BigInt;
use num_traits::Zero;
use std::sync::Arc;

pub(super) fn eval_builtin_bags(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === Bags module ===
        "EmptyBag" => {
            // EmptyBag - the empty bag (empty function)
            check_arity(name, args, 0, span)?;
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                vec![],
            )))))
        }

        "IsABag" => {
            // IsABag(B) - check if B is a valid bag (function with positive integer values)
            // In TLA+, a bag is a function from elements to positive integers (counts)
            // Tuples/Sequences are also functions (from 1..n to values), so they can be bags too
            check_arity(name, args, 1, span)?;
            let bv = eval(ctx, &args[0])?;

            // Handle Value::Func
            if let Some(func) = bv.as_func() {
                // Check all values are positive integers
                for v in func.mapping_values() {
                    match v.to_bigint() {
                        Some(n) if n > BigInt::zero() => {}
                        _ => return Ok(Some(Value::Bool(false))),
                    }
                }
                return Ok(Some(Value::Bool(true)));
            }

            // Handle Value::Tuple and Value::Seq
            // These are functions from 1..n to values
            if let Some(seq) = bv.as_seq() {
                // Check all values are positive integers
                for v in seq.iter() {
                    match v.to_bigint() {
                        Some(n) if n > BigInt::zero() => {}
                        _ => return Ok(Some(Value::Bool(false))),
                    }
                }
                return Ok(Some(Value::Bool(true)));
            }

            // Handle Value::IntFunc (integer-keyed function)
            if let Value::IntFunc(int_func) = &bv {
                for v in int_func.values() {
                    match v.to_bigint() {
                        Some(n) if n > BigInt::zero() => {}
                        _ => return Ok(Some(Value::Bool(false))),
                    }
                }
                return Ok(Some(Value::Bool(true)));
            }

            // Handle Value::Record (records are functions from string keys to values)
            if let Some(rec) = bv.as_record() {
                for v in rec.values() {
                    match v.to_bigint() {
                        Some(n) if n > BigInt::zero() => {}
                        _ => return Ok(Some(Value::Bool(false))),
                    }
                }
                return Ok(Some(Value::Bool(true)));
            }

            // Not a function-like value
            Ok(Some(Value::Bool(false)))
        }

        "SetToBag" => {
            // SetToBag(S) - convert set to bag (each element has count 1)
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // #1828: Use eval_iter_set for SetPred-aware iteration.
            let set_iter = eval_iter_set(ctx, &sv, Some(args[0].span))?;
            let mut entries: Vec<(Value, Value)> = Vec::new();
            for elem in set_iter {
                entries.push((elem.clone(), Value::SmallInt(1)));
            }
            // Sort entries - iteration order may not be sorted
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        "BagToSet" => {
            // BagToSet(B) - get the underlying set (domain of bag)
            check_arity(name, args, 1, span)?;
            let bv = eval(ctx, &args[0])?;
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;
            let domain: Vec<Value> = func.domain_iter().cloned().collect();
            Ok(Some(Value::Set(Arc::new(SortedSet::from_sorted_vec(
                domain,
            )))))
        }

        "BagIn" => {
            // BagIn(e, B) - is e in bag B with count > 0
            check_arity(name, args, 2, span)?;
            let ev = eval(ctx, &args[0])?;
            let bv = eval(ctx, &args[1])?;
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[1].span)))?;
            match func.mapping_get(&ev) {
                Some(count) => {
                    let n = count
                        .to_bigint()
                        .ok_or_else(|| EvalError::type_error("Int", count, span))?;
                    Ok(Some(Value::Bool(n > BigInt::zero())))
                }
                None => Ok(Some(Value::Bool(false))),
            }
        }

        "CopiesIn" => {
            // CopiesIn(e, B) - count of e in bag B (0 if not present)
            check_arity(name, args, 2, span)?;
            let ev = eval(ctx, &args[0])?;
            let bv = eval(ctx, &args[1])?;
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[1].span)))?;
            match func.mapping_get(&ev) {
                Some(count) => Ok(Some(count.clone())),
                None => Ok(Some(Value::SmallInt(0))),
            }
        }

        "BagCardinality" => {
            // BagCardinality(B) - total count of all elements
            check_arity(name, args, 1, span)?;
            let bv = eval(ctx, &args[0])?;
            let func = bv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;
            let mut total = BigInt::zero();
            for v in func.mapping_values() {
                let n = v
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", v, span))?;
                if n <= BigInt::zero() {
                    return Err(EvalError::Internal {
                        message: "BagCardinality expects a bag (positive integer counts)".into(),
                        span,
                    });
                }
                total += n;
            }
            Ok(Some(Value::big_int(total)))
        }

        "BagCup" | "\\oplus" => {
            // BagCup(B1, B2) or B1 (+) B2 - bag union (add counts)
            check_arity(name, args, 2, span)?;
            let bv1 = eval(ctx, &args[0])?;
            let bv2 = eval(ctx, &args[1])?;
            let func1 = bv1
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv1, Some(args[0].span)))?;
            let func2 = bv2
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv2, Some(args[1].span)))?;

            // Build new mapping: combine counts
            let mut entries: Vec<(Value, Value)> = func1
                .iter()
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect();
            // Value's interior mutability (fingerprint cache) doesn't affect Hash/Eq
            // Part of #4112: FxHashMap for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let mut entries_map: rustc_hash::FxHashMap<Value, usize> = entries
                .iter()
                .enumerate()
                .map(|(i, (k, _))| (k.clone(), i))
                .collect();

            for (key, val2) in func2.mapping_iter() {
                let n2 = val2
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", val2, span))?;
                if let Some(&idx) = entries_map.get(key) {
                    let n1 = entries[idx]
                        .1
                        .to_bigint()
                        .ok_or_else(|| EvalError::type_error("Int", &entries[idx].1, span))?;
                    entries[idx].1 = Value::big_int(n1 + n2);
                } else {
                    let idx = entries.len();
                    entries.push((key.clone(), Value::big_int(n2.clone())));
                    entries_map.insert(key.clone(), idx);
                }
            }
            // Sort by key
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        "BagDiff" | "\\ominus" => {
            // BagDiff(B1, B2) or B1 (-) B2 - bag difference (subtract counts)
            check_arity(name, args, 2, span)?;
            let bv1 = eval(ctx, &args[0])?;
            let bv2 = eval(ctx, &args[1])?;
            let func1 = bv1
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv1, Some(args[0].span)))?;
            let func2 = bv2
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Bag/Function", &bv2, Some(args[1].span)))?;

            let mut entries: Vec<(Value, Value)> = Vec::new();

            for (key, val1) in func1.mapping_iter() {
                let n1 = val1
                    .to_bigint()
                    .ok_or_else(|| EvalError::type_error("Int", val1, span))?;
                let diff = match func2.mapping_get(key) {
                    Some(val2) => {
                        let n2 = val2
                            .to_bigint()
                            .ok_or_else(|| EvalError::type_error("Int", val2, span))?;
                        n1 - n2
                    }
                    None => n1.clone(),
                };
                if diff > BigInt::zero() {
                    entries.push((key.clone(), Value::big_int(diff)));
                }
            }
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        // Combinatorial operations delegated to submodule
        "BagUnion" => combinatorial::eval_bag_union(ctx, args, span),
        "BagOfAll" => combinatorial::eval_bag_of_all(ctx, args, span),
        "SubBag" => combinatorial::eval_sub_bag(ctx, args, span),
        "SqSubseteq" | "\\sqsubseteq" => combinatorial::eval_sq_subseteq(ctx, args, span),

        // Not handled by this domain
        _ => Ok(None),
    }
}
