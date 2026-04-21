// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    apply_builtin_binary_op, check_arity, count_set_filter_elements, eval, eval_iter_set, EvalCtx,
    EvalError, EvalResult, Expr, FuncValue, KSubsetValue, Span, Spanned, Value,
};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::sync::Arc;

pub(super) fn eval_builtin_finite_sets(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === FiniteSets ===
        "Cardinality" => {
            check_arity(name, args, 1, span)?;

            // Optimization: For set filter expressions {x \in S : P(x)}, count directly
            // without building the intermediate set. This is especially important for
            // patterns like Cardinality({m \in rcvd'[self] : m[2] = "ECHO0"}) in bosco.
            if let Expr::SetFilter(bound, pred) = &args[0].node {
                if let Some(domain_expr) = &bound.domain {
                    let domain_val = eval(ctx, domain_expr)?;
                    let count_result =
                        count_set_filter_elements(ctx, &domain_val, bound, pred, span);
                    if let Some(count) = count_result? {
                        return Ok(Some(Value::int(count as i64)));
                    }
                }
            }

            // Fall back to standard evaluation for non-filter sets
            let sv = eval(ctx, &args[0])?;
            // Part of #3978: Streaming SetPred cardinality -- count elements by
            // streaming through the source set and evaluating the predicate,
            // without materializing the full filtered set into a Vec<Value>.
            // Falls back to the materializing path when special optimizations
            // (SUBSET filter, K-subset, funcset partition) apply.
            if let Value::SetPred(ref spv) = sv {
                if let Some(count) = crate::helpers::count_setpred_streaming(ctx, spv)? {
                    return Ok(Some(Value::int(count as i64)));
                }
                // Fall back: special optimizations active, materialize via eval_iter_set.
                let count = eval_iter_set(ctx, &sv, span)?.count();
                return Ok(Some(Value::int(count as i64)));
            }
            match sv.set_len() {
                Some(n) => Ok(Some(Value::big_int(n))),
                None if sv.is_set() => Err(EvalError::Internal {
                    message: "Cardinality not supported for this set value".into(),
                    span,
                }),
                None => Err(EvalError::type_error("Set", &sv, Some(args[0].span))),
            }
        }

        "IsFiniteSet" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // #1508: Check semantic finiteness, not just set-ness.
            // Nat, Int, Real, STRING, Seq(S) are infinite sets.
            Ok(Some(Value::Bool(sv.is_finite_set())))
        }

        // === FiniteSetsExt operators ===

        // Quantify(S, P) - count elements of S satisfying predicate P
        "Quantify" => {
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;

            // Get the predicate operator name from the second argument
            let pred_name = match &args[1].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "Quantify requires an operator name as second argument".into(),
                        span,
                    });
                }
            };

            // Get the operator definition
            let pred_def = ctx
                .get_op(&pred_name)
                .ok_or_else(|| EvalError::UndefinedOp {
                    name: pred_name.clone(),
                    span,
                })?;

            if pred_def.params.len() != 1 {
                return Err(EvalError::ArityMismatch {
                    op: pred_name,
                    expected: 1,
                    got: pred_def.params.len(),
                    span,
                });
            }

            let mut count = 0i64;
            // #1899: Use eval_iter_set for SetPred-transparent iteration
            for elem in eval_iter_set(ctx, &sv, Some(args[0].span))? {
                let new_ctx = ctx.bind(pred_def.params[0].name.node.as_str(), elem);
                let result = eval(&new_ctx, &pred_def.body)?;
                match result {
                    Value::Bool(true) => count += 1,
                    Value::Bool(false) => {}
                    other => {
                        // TLC: "Evaluating predicate <pred> yielded non-Boolean value."
                        return Err(EvalError::TypeError {
                            expected: "BOOLEAN",
                            got: other.type_name(),
                            span,
                        });
                    }
                }
            }
            Ok(Some(Value::int(count)))
        }

        // Ksubsets(S, k) - all k-element subsets of S
        // Returns a lazy KSubsetValue for efficient membership checking
        "Ksubsets" => {
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            // Accept any set-like value (Set, Interval, etc.)
            if !sv.is_set() {
                return Err(EvalError::type_error("Set", &sv, Some(args[0].span)));
            }
            let kv = eval(ctx, &args[1])?;
            let k_bigint = kv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &kv, Some(args[1].span)))?;

            // Part of #2224: TLC throws IllegalArgumentException for negative k.
            // Previously, `-1_i64 as usize` silently wrapped to usize::MAX.
            if k_bigint < BigInt::zero() {
                return Err(EvalError::ArgumentError {
                    position: "second",
                    op: "Ksubsets".to_string(),
                    expected_type: "non-negative integer",
                    value_display: format!("{k_bigint}"),
                    span,
                });
            }

            // Safe: k >= 0. Oversized k (k > |S|) handled downstream in
            // KSubsetValue::len()/to_ord_set()/iter() which return empty results.
            let k = k_bigint.to_usize().unwrap_or(usize::MAX);

            // Return lazy KSubsetValue - enumeration happens on-demand
            Ok(Some(Value::KSubset(KSubsetValue::new(sv, k))))
        }

        // SymDiff(S, T) - symmetric difference: (S \ T) \cup (T \ S)
        "SymDiff" => {
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let sv2 = eval(ctx, &args[1])?;
            // #1899: collect via eval_iter_set for SetPred transparency
            // Part of #4112: FxHashSet for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let elems1: rustc_hash::FxHashSet<Value> =
                eval_iter_set(ctx, &sv1, Some(args[0].span))?.collect();
            #[allow(clippy::mutable_key_type)]
            let elems2: rustc_hash::FxHashSet<Value> =
                eval_iter_set(ctx, &sv2, Some(args[1].span))?.collect();
            let mut result = Vec::new();
            for elem in &elems1 {
                if !elems2.contains(elem) {
                    result.push(elem.clone());
                }
            }
            for elem in &elems2 {
                if !elems1.contains(elem) {
                    result.push(elem.clone());
                }
            }
            Ok(Some(Value::set(result)))
        }

        // Flatten(SS) - union of a set of sets
        "Flatten" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // #1899: Use eval_iter_set for outer and inner sets (SetPred transparency)
            let mut result = Vec::new();
            #[allow(clippy::mutable_key_type)]
            let mut seen: rustc_hash::FxHashSet<Value> = rustc_hash::FxHashSet::default();
            for inner in eval_iter_set(ctx, &sv, Some(args[0].span))? {
                for elem in eval_iter_set(ctx, &inner, Some(args[0].span))? {
                    if seen.insert(elem.clone()) {
                        result.push(elem);
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // Choose(S) - return an arbitrary element of S (first in sorted order)
        "Choose" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // #1899: Use eval_iter_set for SetPred transparency
            let mut iter = eval_iter_set(ctx, &sv, Some(args[0].span))?;
            iter.next()
                .ok_or_else(|| EvalError::Internal {
                    message: "Choose requires non-empty set".into(),
                    span,
                })
                .map(Some)
        }

        // Sum(S) - sum of all elements in a set of integers
        "Sum" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let mut total = BigInt::zero();
            for elem in eval_iter_set(ctx, &sv, Some(args[0].span))? {
                if let Some(n) = elem.to_bigint() {
                    total += n;
                } else {
                    return Err(EvalError::type_error("Int", &elem, Some(args[0].span)));
                }
            }
            Ok(Some(Value::big_int(total)))
        }

        // Product(S) - product of all elements in a set of integers
        "Product" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let mut total = BigInt::one();
            for elem in eval_iter_set(ctx, &sv, Some(args[0].span))? {
                if let Some(n) = elem.to_bigint() {
                    total *= n;
                } else {
                    return Err(EvalError::type_error("Int", &elem, Some(args[0].span)));
                }
            }
            Ok(Some(Value::big_int(total)))
        }

        // ReduceSet(op, S, base) - like FoldSet but different argument order
        // Part of #3075: Supports both user-defined operators (Expr::Ident) and
        // built-in operator references (Expr::OpRef) like \intersect, \cup, +, etc.
        "ReduceSet" => {
            check_arity(name, args, 3, span)?;

            let sv = eval(ctx, &args[1])?;
            let base = eval(ctx, &args[2])?;

            // Resolve the operator from the first argument
            let mut result = base;
            match &args[0].node {
                Expr::Ident(op_name, _) => {
                    let op_def = ctx.get_op(op_name).ok_or_else(|| EvalError::UndefinedOp {
                        name: op_name.clone(),
                        span,
                    })?;
                    if op_def.params.len() != 2 {
                        return Err(EvalError::ArityMismatch {
                            op: op_name.clone(),
                            expected: 2,
                            got: op_def.params.len(),
                            span,
                        });
                    }
                    // #1899: Use eval_iter_set for SetPred-transparent iteration
                    for elem in eval_iter_set(ctx, &sv, Some(args[1].span))? {
                        let new_ctx = ctx.bind2(
                            op_def.params[0].name.node.as_str(),
                            result,
                            op_def.params[1].name.node.as_str(),
                            elem,
                        );
                        result = eval(&new_ctx, &op_def.body)?;
                    }
                }
                Expr::OpRef(op) => {
                    // Built-in operator reference (e.g., \intersect, \cup, +).
                    // Apply directly via apply_builtin_binary_op — O(n) fold.
                    for elem in eval_iter_set(ctx, &sv, Some(args[1].span))? {
                        result = apply_builtin_binary_op(op, result, elem, span)?;
                    }
                }
                _ => {
                    return Err(EvalError::Internal {
                        message: "ReduceSet requires operator name as first argument".into(),
                        span,
                    });
                }
            }

            Ok(Some(result))
        }

        // Mean(S) - average of a set of integers (integer division)
        "Mean" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // #1899: Use eval_iter_set for SetPred-transparent iteration
            let mut total = BigInt::zero();
            let mut count = BigInt::zero();
            for elem in eval_iter_set(ctx, &sv, Some(args[0].span))? {
                if let Some(n) = elem.to_bigint() {
                    total += n;
                    count += 1;
                } else {
                    return Err(EvalError::type_error("Int", &elem, Some(args[0].span)));
                }
            }
            if count.is_zero() {
                return Err(EvalError::Internal {
                    message: "Mean requires non-empty set".into(),
                    span,
                });
            }
            use num_integer::Integer;
            Ok(Some(Value::big_int(total.div_floor(&count))))
        }

        // MapThenSumSet(Op, S) - map a unary operator over a set, then sum the results
        // MapThenSumSet(Op, S) == LET R == {Op(x) : x \in S} IN Sum(R)
        "MapThenSumSet" => {
            check_arity(name, args, 2, span)?;

            // Get the operator name from the first argument
            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "MapThenSumSet requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let sv = eval(ctx, &args[1])?;

            // Get the operator definition
            let op_def = ctx.get_op(&op_name).ok_or_else(|| EvalError::UndefinedOp {
                name: op_name.clone(),
                span,
            })?;

            if op_def.params.len() != 1 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 1,
                    got: op_def.params.len(),
                    span,
                });
            }

            // #1899: Use eval_iter_set for SetPred-transparent iteration
            let mut total = BigInt::zero();
            for elem in eval_iter_set(ctx, &sv, Some(args[1].span))? {
                let new_ctx = ctx.bind(op_def.params[0].name.node.as_str(), elem);
                let mapped = eval(&new_ctx, &op_def.body)?;
                if let Some(n) = mapped.to_bigint() {
                    total += n;
                } else {
                    return Err(EvalError::type_error("Int", &mapped, Some(args[0].span)));
                }
            }
            Ok(Some(Value::big_int(total)))
        }

        // Choices(SS) - the set of all choice functions for a set of sets
        // Choices(SS) == { f \in [SS -> UNION SS] : \A S \in SS : f[S] \in S }
        // For each set S in SS, f picks one element from S.
        "Choices" => {
            check_arity(name, args, 1, span)?;
            let ssv = eval(ctx, &args[0])?;
            // #1899: Use eval_iter_set for SetPred-transparent iteration (outer + inner)
            let mut sets_vec: Vec<(Value, Vec<Value>)> = Vec::new();
            for s in eval_iter_set(ctx, &ssv, Some(args[0].span))? {
                let elems: Vec<Value> = eval_iter_set(ctx, &s, Some(args[0].span))?.collect();
                if elems.is_empty() {
                    return Ok(Some(Value::set(vec![])));
                }
                sets_vec.push((s, elems));
            }

            if sets_vec.is_empty() {
                // Empty set of sets -> one choice function: the empty function.
                // Use Value::Seq (empty sequence) rather than Value::Func so the
                // representation is consistent with eval_func_def's empty-domain
                // path, avoiding SET_INTERN_TABLE variant substitution when the
                // empty tuple <<>> and empty function [] share the same hash and
                // PartialEq (they are semantically equal in TLA+). (#1700)
                return Ok(Some(Value::set(vec![Value::Seq(Arc::new(
                    Vec::new().into(),
                ))])));
            }

            // Sort by key so we can build sorted entries directly
            sets_vec.sort_by(|(a, _), (b, _)| a.cmp(b));

            // Generate all combinations using cartesian product
            let mut result_functions: Vec<Value> = Vec::new();
            let mut indices: Vec<usize> = vec![0; sets_vec.len()];

            loop {
                // Build a function from the current indices - entries are already sorted
                let entries: Vec<(Value, Value)> = sets_vec
                    .iter()
                    .enumerate()
                    .map(|(i, (set_key, elements))| (set_key.clone(), elements[indices[i]].clone()))
                    .collect();
                result_functions.push(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                    entries,
                ))));

                // Advance indices (like incrementing a multi-digit counter)
                let mut pos = sets_vec.len();
                loop {
                    if pos == 0 {
                        // Done - all combinations exhausted
                        return Ok(Some(Value::set(result_functions)));
                    }
                    pos -= 1;
                    indices[pos] += 1;
                    if indices[pos] < sets_vec[pos].1.len() {
                        break;
                    }
                    indices[pos] = 0;
                }
            }
        }

        // ChooseUnique(S, P) - the unique element of S satisfying predicate P
        // Requires exactly one element satisfies P, otherwise error
        "ChooseUnique" => {
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;

            // Get the predicate (should be a lambda with one parameter)
            let (param, pred_body) = match &args[1].node {
                Expr::Lambda(params, body) if params.len() == 1 => {
                    (params[0].node.clone(), body.as_ref())
                }
                _ => {
                    return Err(EvalError::Internal {
                        message: "ChooseUnique requires a lambda predicate as second argument"
                            .into(),
                        span,
                    });
                }
            };

            // #1899: Use eval_iter_set for SetPred-transparent iteration
            let mut found: Option<Value> = None;
            for elem in eval_iter_set(ctx, &sv, Some(args[0].span))? {
                let pred_ctx = ctx.bind(param.as_str(), elem.clone());
                let pred_result = eval(&pred_ctx, pred_body)?;
                if pred_result
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &pred_result, span))?
                {
                    if found.is_some() {
                        return Err(EvalError::Internal {
                            message: "ChooseUnique: more than one element satisfies predicate"
                                .into(),
                            span,
                        });
                    }
                    found = Some(elem);
                }
            }

            found
                .ok_or_else(|| EvalError::Internal {
                    message: "ChooseUnique: no element satisfies predicate".into(),
                    span,
                })
                .map(Some)
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
