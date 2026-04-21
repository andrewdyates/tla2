// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    apply_binary_op, check_arity, eval, eval_iter_set, eval_iter_set_tlc_normalized, EvalCtx,
    EvalError, EvalResult, Expr, OperatorRef, SortedSet, Span, Spanned, Value,
};
use std::sync::Arc;
// SequencesExt module operators — basic operations and sequence-level folds

pub(super) fn eval_builtin_sequences_ext(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "Reverse" => {
            // Reverse(s) - reverse the elements of a sequence
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let reversed: Vec<Value> = seq.iter().rev().cloned().collect();
            Ok(Some(Value::Seq(Arc::new(reversed.into()))))
        }

        "Front" => {
            // Front(s) - all but the last element (opposite of Tail)
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // Fast path: use O(log n) front for SeqValue
            if let Some(seq_value) = sv.as_seq_value() {
                if seq_value.is_empty() {
                    return Err(EvalError::IndexOutOfBounds {
                        index: 1,
                        len: 0,
                        value_display: None,
                        span,
                    });
                }
                return Ok(Some(Value::Seq(Arc::new(seq_value.front()))));
            }
            // Fallback for Tuple
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            if seq.is_empty() {
                return Err(EvalError::IndexOutOfBounds {
                    index: 1,
                    len: 0,
                    value_display: None,
                    span,
                });
            }
            Ok(Some(Value::Seq(Arc::new(
                seq[..seq.len() - 1].to_vec().into(),
            ))))
        }

        "Last" => {
            // Last(s) - the last element of a sequence
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            Ok(Some(seq.last().cloned().ok_or(
                EvalError::IndexOutOfBounds {
                    index: 1,
                    len: 0,
                    value_display: None,
                    span,
                },
            )?))
        }

        "SetToSeq" => {
            // SetToSeq(S) - convert a set to a sequence in TLC-canonical order.
            // Part of #2987: use TLC-normalized order so sequence matches TLC output.
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq: Vec<Value> =
                eval_iter_set_tlc_normalized(ctx, &sv, Some(args[0].span))?.collect();
            Ok(Some(Value::Seq(Arc::new(seq.into()))))
        }

        "SetToSortSeq" => {
            // SetToSortSeq(S, Op) - convert set to sequence sorted by comparator Op
            // Op(a, b) should return TRUE iff a < b
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;

            // Comparator can be a user-defined operator name (Ident) or a built-in operator
            // reference (OpRef) like <, <=, etc.
            let cmp_op = match &args[1].node {
                Expr::Ident(name, _) => OperatorRef::UserDefined(name.clone()),
                Expr::OpRef(op) => OperatorRef::BuiltIn(op.clone()),
                _ => {
                    return Err(EvalError::Internal {
                        message: "SetToSortSeq requires an operator as second argument".into(),
                        span,
                    });
                }
            };

            // Collect and sort elements using the comparator
            let mut elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            // Use a simple insertion sort with the custom comparator
            for i in 1..elements.len() {
                let mut j = i;
                while j > 0 {
                    let cmp_result = apply_binary_op(
                        ctx,
                        &cmp_op,
                        elements[j - 1].clone(),
                        elements[j].clone(),
                        span,
                    )?;
                    let a_before_b = cmp_result
                        .as_bool()
                        .ok_or_else(|| EvalError::type_error("BOOLEAN", &cmp_result, span))?;
                    if a_before_b {
                        break;
                    }
                    elements.swap(j - 1, j);
                    j -= 1;
                }
            }
            Ok(Some(Value::Seq(Arc::new(elements.into()))))
        }

        "ToSet" => {
            // ToSet(s) - convert sequence to set (range of sequence values)
            // ToSet(s) == { s[i] : i \in DOMAIN s }
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let set: Vec<Value> = seq.iter().cloned().collect();
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(set)))))
        }

        "Cons" => {
            // Cons(e, s) - prepend element e to sequence s
            // Cons(e, s) == <<e>> \o s
            check_arity(name, args, 2, span)?;
            let elem = eval(ctx, &args[0])?;
            let sv = eval(ctx, &args[1])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[1].span)))?;
            let mut new_seq = vec![elem];
            new_seq.extend(seq.iter().cloned());
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        "Contains" => {
            // Contains(s, e) - TRUE if sequence s contains element e
            // Contains(s, e) == \E i \in DOMAIN s : s[i] = e
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let elem = eval(ctx, &args[1])?;
            Ok(Some(Value::Bool(seq.contains(&elem))))
        }

        "IsPrefix" => {
            // IsPrefix(s, t) - TRUE if s is a prefix of t
            // IsPrefix(s, t) == SubSeq(t, 1, Len(s)) = s
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let seq1 = sv1
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv1, Some(args[0].span)))?;
            let sv2 = eval(ctx, &args[1])?;
            let seq2 = sv2
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv2, Some(args[1].span)))?;
            let is_prefix = seq2.len() >= seq1.len() && seq1[..] == seq2[..seq1.len()];
            Ok(Some(Value::Bool(is_prefix)))
        }

        "IsSuffix" => {
            // IsSuffix(s, t) - TRUE if s is a suffix of t
            // IsSuffix(s, t) == SubSeq(t, Len(t) - Len(s) + 1, Len(t)) = s
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let seq1 = sv1
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv1, Some(args[0].span)))?;
            let sv2 = eval(ctx, &args[1])?;
            let seq2 = sv2
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv2, Some(args[1].span)))?;
            let is_suffix = seq2.len() >= seq1.len() && seq1[..] == seq2[seq2.len() - seq1.len()..];
            Ok(Some(Value::Bool(is_suffix)))
        }

        "IsStrictPrefix" => {
            // IsStrictPrefix(s, t) - TRUE if s is a strict prefix of t (s != t)
            // IsStrictPrefix(s, t) == IsPrefix(s, t) /\ s /= t
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let seq1 = sv1
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv1, Some(args[0].span)))?;
            let sv2 = eval(ctx, &args[1])?;
            let seq2 = sv2
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv2, Some(args[1].span)))?;
            let is_strict_prefix = seq1.len() < seq2.len() && seq1[..] == seq2[..seq1.len()];
            Ok(Some(Value::Bool(is_strict_prefix)))
        }

        "IsStrictSuffix" => {
            // IsStrictSuffix(s, t) - TRUE if s is a strict suffix of t (s != t)
            // IsStrictSuffix(s, t) == IsSuffix(s, t) /\ s /= t
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let seq1 = sv1
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv1, Some(args[0].span)))?;
            let sv2 = eval(ctx, &args[1])?;
            let seq2 = sv2
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv2, Some(args[1].span)))?;
            let is_strict_suffix =
                seq1.len() < seq2.len() && seq1[..] == seq2[seq2.len() - seq1.len()..];
            Ok(Some(Value::Bool(is_strict_suffix)))
        }

        "Snoc" => {
            // Snoc(s, e) - append element e to sequence s (opposite of Cons)
            // Snoc(s, e) == Append(s, e)
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let elem = eval(ctx, &args[1])?;
            // Fast path: use O(log n) append for SeqValue
            if let Some(seq_value) = sv.as_seq_value() {
                return Ok(Some(Value::Seq(Arc::new(seq_value.append(elem)))));
            }
            // Fallback for Tuple
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;
            let mut new_seq: Vec<Value> = seq.to_vec();
            new_seq.push(elem);
            Ok(Some(Value::Seq(Arc::new(new_seq.into()))))
        }

        "FoldLeftDomain" => {
            // FoldLeftDomain(Op, base, s) - fold left with index available
            // Op(acc, elem, idx) where idx is 1-indexed
            check_arity(name, args, 3, span)?;

            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldLeftDomain requires operator name as first argument".into(),
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

            if op_def.params.len() != 3 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 3,
                    got: op_def.params.len(),
                    span,
                });
            }

            let mut result = base;
            for (i, elem) in seq.iter().enumerate() {
                let idx = Value::SmallInt(i as i64 + 1); // 1-indexed
                let new_ctx = ctx.bind3(
                    op_def.params[0].name.node.as_str(),
                    result,
                    op_def.params[1].name.node.as_str(),
                    elem.clone(),
                    op_def.params[2].name.node.as_str(),
                    idx,
                );
                result = eval(&new_ctx, &op_def.body)?;
            }
            Ok(Some(result))
        }

        "FoldRightDomain" => {
            // FoldRightDomain(Op, s, base) - fold right with index available
            // Op(elem, acc, idx) where idx is 1-indexed
            check_arity(name, args, 3, span)?;

            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "FoldRightDomain requires operator name as first argument".into(),
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

            if op_def.params.len() != 3 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 3,
                    got: op_def.params.len(),
                    span,
                });
            }

            // Fold from right to left, indices are still from original sequence
            let mut result = base;
            for (i, elem) in seq.iter().enumerate().rev() {
                let idx = Value::SmallInt(i as i64 + 1); // 1-indexed
                let new_ctx = ctx.bind3(
                    op_def.params[0].name.node.as_str(),
                    elem.clone(),
                    op_def.params[1].name.node.as_str(),
                    result,
                    op_def.params[2].name.node.as_str(),
                    idx,
                );
                result = eval(&new_ctx, &op_def.body)?;
            }
            Ok(Some(result))
        }

        "LongestCommonPrefix" => {
            // LongestCommonPrefix(seqs) - longest common prefix of a set of sequences
            // LongestCommonPrefix({<<1,2,3>>, <<1,2,4>>}) == <<1,2>>
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seqs_set: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();

            if seqs_set.is_empty() {
                // Empty set -> empty sequence
                return Ok(Some(Value::Seq(Arc::new(Vec::new().into()))));
            }

            // Get all sequences from the set
            let seqs: Vec<std::borrow::Cow<'_, [Value]>> = seqs_set
                .iter()
                .map(|v| {
                    v.as_seq()
                        .ok_or_else(|| EvalError::type_error("Seq", v, Some(args[0].span)))
                })
                .collect::<Result<Vec<_>, _>>()?;

            if seqs.is_empty() {
                return Ok(Some(Value::Seq(Arc::new(Vec::new().into()))));
            }

            // Find the minimum length
            let min_len = seqs.iter().map(|s| s.len()).min().unwrap_or(0);

            // Find the longest common prefix
            let mut lcp_len = 0;
            for i in 0..min_len {
                let first_elem = &seqs[0][i];
                if seqs.iter().all(|s| &s[i] == first_elem) {
                    lcp_len = i + 1;
                } else {
                    break;
                }
            }

            let lcp: Vec<Value> = seqs[0][..lcp_len].to_vec();
            Ok(Some(Value::Seq(Arc::new(lcp.into()))))
        }

        "CommonPrefixes" => {
            // CommonPrefixes(seqs) - set of all common prefixes of a set of sequences
            // CommonPrefixes({<<1,2,3>>, <<1,2,4>>}) == { <<>>, <<1>>, <<1,2>> }
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let seqs_set: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();

            if seqs_set.is_empty() {
                // Empty set -> set containing only empty sequence
                return Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(vec![
                    Value::Seq(Arc::new(Vec::new().into())),
                ])))));
            }

            // Get all sequences from the set
            let seqs: Vec<std::borrow::Cow<'_, [Value]>> = seqs_set
                .iter()
                .map(|v| {
                    v.as_seq()
                        .ok_or_else(|| EvalError::type_error("Seq", v, Some(args[0].span)))
                })
                .collect::<Result<Vec<_>, _>>()?;

            // Find minimum length for potential common prefixes
            let min_len = seqs.iter().map(|s| s.len()).min().unwrap_or(0);

            // Find all common prefixes up to LCP
            let mut result: Vec<Value> = Vec::new();
            result.push(Value::Seq(Arc::new(Vec::new().into()))); // Empty sequence is always a common prefix

            for len in 1..=min_len {
                let prefix = &seqs[0][..len];
                if seqs
                    .iter()
                    .all(|s| s.len() >= len && s[..len] == prefix[..])
                {
                    result.push(Value::Seq(Arc::new(prefix.to_vec().into())));
                } else {
                    break; // Once we find a non-common prefix, no longer ones can be common
                }
            }

            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        "FlattenSeq" => {
            // FlattenSeq(ss) - flatten a sequence of sequences into a single sequence
            // FlattenSeq(<<s1, s2, ...>>) == s1 \o s2 \o ...
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let outer_seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;

            let mut result: Vec<Value> = Vec::new();
            for inner in outer_seq.iter() {
                let inner_seq = inner
                    .as_seq()
                    .ok_or_else(|| EvalError::type_error("Seq", inner, Some(args[0].span)))?;
                result.extend(inner_seq.iter().cloned());
            }
            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        "Zip" => {
            // Zip(s, t) - zip two sequences into a sequence of pairs
            // Zip(<<a,b>>, <<1,2>>) == << <<a,1>>, <<b,2>> >>
            // Result length is min(Len(s), Len(t))
            check_arity(name, args, 2, span)?;
            let sv1 = eval(ctx, &args[0])?;
            let seq1 = sv1
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv1, Some(args[0].span)))?;
            let sv2 = eval(ctx, &args[1])?;
            let seq2 = sv2
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv2, Some(args[1].span)))?;

            let result: Vec<Value> = seq1
                .iter()
                .zip(seq2.iter())
                .map(|(a, b)| Value::Tuple(vec![a.clone(), b.clone()].into()))
                .collect();
            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        _ => Ok(None),
    }
}
