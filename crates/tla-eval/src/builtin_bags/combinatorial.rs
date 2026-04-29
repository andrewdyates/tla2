// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Combinatorial bag operations: BagUnion, BagOfAll, SubBag, SqSubseteq.
//!
//! Extracted from `builtin_bags.rs` as part of #3463.

use super::super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, FuncValue, SortedSet,
    Span, Spanned, Value,
};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use std::sync::Arc;

pub(super) fn eval_bag_union(
    ctx: &EvalCtx,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    // BagUnion(S) - bag union of all elements in set S of bags
    check_arity("BagUnion", args, 1, span)?;
    let sv = eval(ctx, &args[0])?;
    // #1828: Use eval_iter_set for SetPred-aware iteration.
    let set_iter = eval_iter_set(ctx, &sv, Some(args[0].span))?;

    // Value's interior mutability (fingerprint cache) doesn't affect Hash/Eq
    #[allow(clippy::mutable_key_type)]
    let mut counts: rustc_hash::FxHashMap<Value, BigInt> = rustc_hash::FxHashMap::default();

    for bag in set_iter {
        let func = bag
            .to_func_coerced()
            .ok_or_else(|| EvalError::type_error("Bag/Function", &bag, Some(args[0].span)))?;
        for (key, val) in func.mapping_iter() {
            let n = val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", val, span))?;
            if n <= BigInt::zero() {
                return Err(EvalError::Internal {
                    message: "BagUnion expects a set of bags (positive integer counts)".into(),
                    span,
                });
            }
            *counts.entry(key.clone()).or_insert_with(BigInt::zero) += n;
        }
    }

    let mut entries: Vec<(Value, Value)> = counts
        .into_iter()
        .map(|(k, v)| (k, Value::big_int(v)))
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
        entries,
    )))))
}

pub(super) fn eval_bag_of_all(
    ctx: &EvalCtx,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    // BagOfAll(F(_), B) - map bag elements through unary operator, preserving counts
    check_arity("BagOfAll", args, 2, span)?;

    fn eval_unary_bag_map(
        ctx: &EvalCtx,
        op: &Spanned<Expr>,
        arg_value: Value,
        span: Option<Span>,
    ) -> EvalResult<Value> {
        match &op.node {
            Expr::Lambda(params, body) => {
                if params.len() != 1 {
                    return Err(EvalError::ArityMismatch {
                        op: "<lambda>".into(),
                        expected: 1,
                        got: params.len(),
                        span,
                    });
                }
                let param_name = params[0].node.clone();
                let new_ctx = ctx.bind(param_name, arg_value);
                eval(&new_ctx, body)
            }
            Expr::Ident(_, _) => {
                // Apply by name/closure via Expr::Apply with a temporary bound variable.
                let tmp = "__tla2_bagofall_arg".to_string();
                let call = Spanned::new(
                    Expr::Apply(
                        Box::new(op.clone()),
                        vec![Spanned::new(
                            Expr::Ident(tmp.clone(), tla_core::name_intern::NameId::INVALID),
                            op.span,
                        )],
                    ),
                    op.span,
                );
                let call_ctx = ctx.bind(tmp, arg_value);
                eval(&call_ctx, &call)
            }
            Expr::ModuleRef(instance, op_name, existing_args) => {
                if !existing_args.is_empty() {
                    return Err(EvalError::Internal {
                        message: "BagOfAll expects an operator reference for its first argument"
                            .into(),
                        span: Some(op.span),
                    });
                }
                let tmp = "__tla2_bagofall_arg".to_string();
                let call = Spanned::new(
                    Expr::ModuleRef(
                        instance.clone(),
                        op_name.clone(),
                        vec![Spanned::new(
                            Expr::Ident(tmp.clone(), tla_core::name_intern::NameId::INVALID),
                            op.span,
                        )],
                    ),
                    op.span,
                );
                let call_ctx = ctx.bind(tmp, arg_value);
                eval(&call_ctx, &call)
            }
            _ => Err(EvalError::Internal {
                message: "BagOfAll expects an operator (name/module ref) or LAMBDA".into(),
                span: Some(op.span),
            }),
        }
    }

    let bv = eval(ctx, &args[1])?;
    let func = bv
        .to_func_coerced()
        .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[1].span)))?;

    // Value's interior mutability (fingerprint cache) doesn't affect Hash/Eq
    #[allow(clippy::mutable_key_type)]
    let mut counts: rustc_hash::FxHashMap<Value, BigInt> = rustc_hash::FxHashMap::default();

    for (key, val) in func.mapping_iter() {
        let n = val
            .to_bigint()
            .ok_or_else(|| EvalError::type_error("Int", val, span))?;
        if n <= BigInt::zero() {
            return Err(EvalError::Internal {
                message: "BagOfAll expects a bag (positive integer counts)".into(),
                span,
            });
        }

        let mapped = eval_unary_bag_map(ctx, &args[0], key.clone(), span)?;

        *counts.entry(mapped).or_insert_with(BigInt::zero) += n;
    }

    let mut entries: Vec<(Value, Value)> = counts
        .into_iter()
        .map(|(k, v)| (k, Value::big_int(v)))
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
        entries,
    )))))
}

pub(super) fn eval_sub_bag(
    ctx: &EvalCtx,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    // SubBag(B) - set of all subbags of bag B
    check_arity("SubBag", args, 1, span)?;
    let bv = eval(ctx, &args[0])?;
    let func = bv
        .to_func_coerced()
        .ok_or_else(|| EvalError::type_error("Bag/Function", &bv, Some(args[0].span)))?;

    // Enumerate all choices of counts (0..=B[e]) for each element e.
    // This is exponential in |DOMAIN B| and can be enormous; TLC also
    // enumerates for finite bags.
    let mut elems: Vec<(Value, u64)> = Vec::new();
    for (key, val) in func.mapping_iter() {
        let n = val
            .to_bigint()
            .ok_or_else(|| EvalError::type_error("Int", val, span))?;
        if n <= BigInt::zero() {
            return Err(EvalError::Internal {
                message: "SubBag expects a bag (positive integer counts)".into(),
                span,
            });
        }
        let max = n.to_u64().ok_or_else(|| EvalError::Internal {
            message: "SubBag count too large to enumerate".into(),
            span,
        })?;
        elems.push((key.clone(), max));
    }

    fn enumerate_subbags(
        elems: &[(Value, u64)],
        idx: usize,
        entries: Vec<(Value, Value)>,
        out: &mut Vec<Value>,
    ) {
        if idx == elems.len() {
            out.push(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            ))));
            return;
        }

        let (elem, max) = &elems[idx];

        // Count 0: element not present
        enumerate_subbags(elems, idx + 1, entries.clone(), out);

        // Counts 1..=max: element present with chosen multiplicity
        for c in 1..=*max {
            let mut next_entries = entries.clone();
            next_entries.push((elem.clone(), Value::SmallInt(c as i64)));
            enumerate_subbags(elems, idx + 1, next_entries, out);
        }
    }

    let mut out = Vec::new();
    enumerate_subbags(&elems, 0, Vec::new(), &mut out);
    Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(out)))))
}

pub(super) fn eval_sq_subseteq(
    ctx: &EvalCtx,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    // SqSubseteq(B1, B2) or B1 \sqsubseteq B2 - bag subset
    // All counts in B1 must be <= corresponding counts in B2
    check_arity("SqSubseteq", args, 2, span)?;
    let bv1 = eval(ctx, &args[0])?;
    let bv2 = eval(ctx, &args[1])?;
    let func1 = bv1
        .to_func_coerced()
        .ok_or_else(|| EvalError::type_error("Bag/Function", &bv1, Some(args[0].span)))?;
    let func2 = bv2
        .to_func_coerced()
        .ok_or_else(|| EvalError::type_error("Bag/Function", &bv2, Some(args[1].span)))?;

    for (key, val1) in func1.mapping_iter() {
        let n1 = val1
            .to_bigint()
            .ok_or_else(|| EvalError::type_error("Int", val1, span))?;
        let n2 = match func2.mapping_get(key) {
            Some(val2) => val2
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", val2, span))?,
            None => BigInt::zero(),
        };
        if n1 > n2 {
            return Ok(Some(Value::Bool(false)));
        }
    }
    Ok(Some(Value::Bool(true)))
}
