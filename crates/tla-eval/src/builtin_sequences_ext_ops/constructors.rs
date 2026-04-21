// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use crate::{IntervalValue, SortedSet};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};

pub(super) fn eval_constructor_ops(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "Prefixes" => {
            // Prefixes(s) - the set of all prefixes of sequence s (including s and <<>>)
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let mut prefixes = Vec::with_capacity(seq.len() + 1);
            for i in 0..=seq.len() {
                prefixes.push(Value::Seq(Arc::new(seq[..i].to_vec().into())));
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(prefixes)))))
        }

        "Suffixes" => {
            // Suffixes(s) - the set of all suffixes of sequence s (including s and <<>>)
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let mut suffixes = Vec::with_capacity(seq.len() + 1);
            for i in 0..=seq.len() {
                suffixes.push(Value::Seq(Arc::new(seq[i..].to_vec().into())));
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(suffixes)))))
        }

        "BoundedSeq" | "SeqOf" => {
            // BoundedSeq(S, n) == UNION { [1..m -> S] : m \in 0..n }
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let nv = eval(ctx, &args[1])?;
            let n = nv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[1].span)))?
                .to_i64()
                .unwrap_or(0);

            if n < 0 {
                return Ok(Some(Value::empty_set()));
            }

            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            let mut all_seqs = Vec::new();

            fn generate_seqs(
                elements: &[Value],
                max_len: usize,
                current: Vec<Value>,
                all: &mut Vec<Value>,
            ) {
                if current.len() <= max_len {
                    all.push(Value::Seq(Arc::new(current.clone().into())));
                    if current.len() < max_len {
                        for e in elements {
                            let mut next = current.clone();
                            next.push(e.clone());
                            generate_seqs(elements, max_len, next, all);
                        }
                    }
                }
            }

            generate_seqs(&elements, n as usize, vec![], &mut all_seqs);
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(all_seqs)))))
        }

        "TupleOf" => {
            // TupleOf(S, n) == [1..n -> S]
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let nv = eval(ctx, &args[1])?;
            let n = nv
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &nv, Some(args[1].span)))?
                .to_i64()
                .unwrap_or(0);

            if n < 0 {
                return Ok(Some(Value::empty_set()));
            }
            if n == 0 {
                let result = vec![Value::Seq(Arc::new(Vec::new().into()))];
                return Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))));
            }

            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            let mut all_tuples = Vec::new();

            fn generate_tuples(
                elements: &[Value],
                n: usize,
                current: Vec<Value>,
                all: &mut Vec<Value>,
            ) {
                if current.len() == n {
                    all.push(Value::Seq(Arc::new(current.into())));
                } else {
                    for e in elements {
                        let mut next = current.clone();
                        next.push(e.clone());
                        generate_tuples(elements, n, next, all);
                    }
                }
            }

            generate_tuples(&elements, n as usize, vec![], &mut all_tuples);
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(all_tuples)))))
        }

        "Indices" => {
            // Indices(s) - the set {1, ..., Len(s)}
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            Ok(Some(Value::Interval(Arc::new(IntervalValue::new(
                BigInt::one(),
                BigInt::from(seq.len() as i64),
            )))))
        }

        _ => Ok(None),
    }
}
