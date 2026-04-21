// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use crate::SortedSet;

pub(super) fn eval_combinatorial_ops(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "Interleave" => {
            // Interleave(s, t) - interleave two sequences
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let seq1 = sv1
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv1, Some(args[0].span)))?;
            let sv2 = eval(ctx, &args[1])?;
            let seq2 = sv2
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv2, Some(args[1].span)))?;

            let max_len = seq1.len().max(seq2.len());
            let mut result: Vec<Value> = Vec::with_capacity(seq1.len() + seq2.len());
            for i in 0..max_len {
                if i < seq1.len() {
                    result.push(seq1[i].clone());
                }
                if i < seq2.len() {
                    result.push(seq2[i].clone());
                }
            }
            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        "SubSeqs" => {
            // SubSeqs(s) - set of all contiguous subsequences of s (including empty sequence)
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;

            let mut subseqs: Vec<Value> = Vec::new();
            subseqs.push(Value::Seq(Arc::new(Vec::new().into())));

            let len = seq.len();
            for start in 0..len {
                for end in (start + 1)..=len {
                    let subseq: Vec<Value> = seq[start..end].to_vec();
                    subseqs.push(Value::Seq(Arc::new(subseq.into())));
                }
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(subseqs)))))
        }

        "SetToSeqs" => {
            // SetToSeqs(S) - set of all permutations (orderings) of set S
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;

            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            let mut result = Vec::new();

            fn generate_permutations(
                elements: &[Value],
                current: &mut Vec<Value>,
                used: &mut Vec<bool>,
                result: &mut Vec<Value>,
            ) {
                if current.len() == elements.len() {
                    result.push(Value::Seq(Arc::new(current.clone().into())));
                    return;
                }
                for i in 0..elements.len() {
                    if !used[i] {
                        used[i] = true;
                        current.push(elements[i].clone());
                        generate_permutations(elements, current, used, result);
                        current.pop();
                        used[i] = false;
                    }
                }
            }

            let mut current = Vec::new();
            let mut used = vec![false; elements.len()];
            generate_permutations(&elements, &mut current, &mut used, &mut result);
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        "AllSubSeqs" => {
            // AllSubSeqs(s) - set of ALL subsequences (not necessarily contiguous)
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;

            let n = seq.len();
            let mut result: Vec<Value> = Vec::with_capacity(1 << n);

            for mask in 0..(1u64 << n) {
                let mut subseq: Vec<Value> = Vec::new();
                for (i, item) in seq.iter().enumerate().take(n) {
                    if mask & (1 << i) != 0 {
                        subseq.push(item.clone());
                    }
                }
                result.push(Value::Seq(Arc::new(subseq.into())));
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        _ => Ok(None),
    }
}
