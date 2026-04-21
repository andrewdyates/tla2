// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use num_traits::ToPrimitive;

use super::super::{
    check_arity, eval as eval_expr, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span,
    Spanned, Value,
};

fn simulation_random_subset(ctx: &EvalCtx, elements: &[Value], k: usize) -> Option<Vec<Value>> {
    if !ctx.simulation_random_active() {
        return None;
    }
    crate::cache::dep_tracking::mark_runtime_nondeterministic(ctx);
    let mut pool = elements.to_vec();
    let mut subset = Vec::with_capacity(k);
    for _ in 0..k {
        let idx = ctx.next_simulation_random_index(pool.len())?;
        subset.push(pool.swap_remove(idx));
    }
    Some(subset)
}

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // RandomSubset(k, S) - return a random k-element subset of S
        // For model checking, we use a deterministic selection based on set elements
        "RandomSubset" => {
            check_arity(name, args, 2, span)?;
            let kv = eval_expr(ctx, &args[0])?;
            let k = kv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &kv, Some(args[0].span)))?
                .to_usize()
                .ok_or_else(|| EvalError::Internal {
                    message: "RandomSubset requires non-negative integer".into(),
                    span,
                })?;
            let sv = eval_expr(ctx, &args[1])?;
            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[1].span))?.collect();
            let n = elements.len();
            // Part of #3078: TLC clamps k to |S| when k > |S| (returns the whole set).
            // Previous tla2 behavior errored, breaking specs like SmokeEWD998.
            let k = k.min(n);

            if let Some(subset) = simulation_random_subset(ctx, &elements, k) {
                return Ok(Some(Value::set(subset)));
            }

            // For model checking, use deterministic selection (first k elements)
            // This ensures reproducibility of counterexamples
            Ok(Some(Value::set(
                elements.into_iter().take(k).collect::<Vec<_>>(),
            )))
        }

        // RandomSetOfSubsets(k, n, S) - return a set of k random subsets of S
        // Each subset has elements selected with probability n/|S|
        // For model checking, we generate deterministic subsets
        "RandomSetOfSubsets" => {
            check_arity(name, args, 3, span)?;
            let kv = eval_expr(ctx, &args[0])?;
            let k = kv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &kv, Some(args[0].span)))?
                .to_usize()
                .ok_or_else(|| EvalError::Internal {
                    message: "RandomSetOfSubsets requires non-negative k".into(),
                    span,
                })?;
            let nv = eval_expr(ctx, &args[1])?;
            let n = nv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[1].span)))?
                .to_usize()
                .ok_or_else(|| EvalError::Internal {
                    message: "RandomSetOfSubsets requires non-negative n".into(),
                    span,
                })?;
            let sv = eval_expr(ctx, &args[2])?;
            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[2].span))?.collect();
            let card = elements.len();
            if card == 0 {
                // Empty set: return set containing only the empty set
                return Ok(Some(Value::set(vec![Value::set(vec![])])));
            }

            if n > card {
                return Err(EvalError::Internal {
                    message: format!("RandomSetOfSubsets: n={n} exceeds set cardinality={card}"),
                    span,
                });
            }

            // For model checking, generate k deterministic subsets of varying sizes.
            let mut subsets = Vec::with_capacity(k);

            if ctx.simulation_random_active() {
                for _ in 0..k {
                    let subset = simulation_random_subset(ctx, &elements, n).unwrap_or_default();
                    subsets.push(Value::set(subset));
                }
            } else {
                for i in 0..k {
                    let mut subset_elems = Vec::new();
                    // Create subset by taking n elements starting at offset i.
                    for j in 0..n {
                        let idx = (i + j) % card;
                        subset_elems.push(elements[idx].clone());
                    }
                    subsets.push(Value::set(subset_elems));
                }
            }

            Ok(Some(Value::set(subsets)))
        }

        // RandomSubsetSet(k, prob_str, S) - like RandomSetOfSubsets but with explicit probability
        // string.
        "RandomSubsetSet" => {
            check_arity(name, args, 3, span)?;
            let kv = eval_expr(ctx, &args[0])?;
            let k = kv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &kv, Some(args[0].span)))?
                .to_usize()
                .ok_or_else(|| EvalError::Internal {
                    message: "RandomSubsetSet requires non-negative k".into(),
                    span,
                })?;
            let prob_sv = eval_expr(ctx, &args[1])?;
            let prob_str = prob_sv
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &prob_sv, Some(args[1].span)))?;
            let prob: f64 = prob_str.parse().map_err(|_| EvalError::Internal {
                message: format!("RandomSubsetSet: cannot parse probability '{prob_str}'"),
                span,
            })?;
            if !(0.0..=1.0).contains(&prob) {
                return Err(EvalError::Internal {
                    message: format!("RandomSubsetSet: probability {prob} must be in range [0, 1]"),
                    span,
                });
            }
            let sv = eval_expr(ctx, &args[2])?;
            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[2].span))?.collect();
            let card = elements.len();
            if card == 0 {
                return Ok(Some(Value::set(vec![Value::set(vec![])])));
            }

            // Derive n from probability: n = floor(prob * card)
            let n = (prob * card as f64).floor() as usize;

            let mut subsets = Vec::with_capacity(k);

            if ctx.simulation_random_active() {
                for _ in 0..k {
                    let subset = simulation_random_subset(ctx, &elements, n).unwrap_or_default();
                    subsets.push(Value::set(subset));
                }
            } else {
                for i in 0..k {
                    let mut subset_elems = Vec::new();
                    for j in 0..n {
                        let idx = (i + j) % card;
                        subset_elems.push(elements[idx].clone());
                    }
                    subsets.push(Value::set(subset_elems));
                }
            }

            Ok(Some(Value::set(subsets)))
        }

        _ => Ok(None),
    }
}
