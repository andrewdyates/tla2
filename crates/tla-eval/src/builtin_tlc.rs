// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    apply_binary_op, check_arity, eval, eval_iter_set, eval_iter_set_tlc_normalized,
    generate_permutation_functions, EvalCtx, EvalError, EvalResult, Expr, FuncValue, OperatorRef,
    SortedSet, Span, Spanned, Value,
};
use crate::builtin_tlc_get::{eval_tlcget, eval_tlcset};
use crate::value::intern_string;
use std::sync::Arc;
use tla_value::value_fingerprint;

// Built-in TLC and TLCExt module operators

pub(super) fn eval_builtin_tlc(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === TLC ===
        "Print" => {
            // Print(out, val) prints "out  val" and returns val (TLC semantics).
            check_arity(name, args, 2, span)?;
            let out = eval(ctx, &args[0])?;
            let val = eval(ctx, &args[1])?;
            // Keep this on stderr to avoid corrupting `--output json` stdout.
            eprintln!("{out}  {val}");
            Ok(Some(val))
        }

        "PrintT" => {
            // PrintT(out) prints out and returns TRUE (TLC semantics).
            check_arity(name, args, 1, span)?;
            let out = eval(ctx, &args[0])?;
            // Keep this on stderr to avoid corrupting `--output json` stdout.
            eprintln!("{out}");
            Ok(Some(Value::Bool(true)))
        }

        "Assert" => {
            check_arity(name, args, 2, span)?;
            let val = eval(ctx, &args[0])?;
            let cond = val
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &val, Some(args[0].span)))?;
            if !cond {
                let msg = eval(ctx, &args[1])?;
                // TLC semantics: Assert throws the message string directly.
                // The Display of AssertionFailed is just the message, no wrapping.
                let message = match msg.as_string() {
                    Some(s) => s.to_string(),
                    None => format!("{msg}"),
                };
                return Err(EvalError::AssertionFailed { message, span });
            }
            Ok(Some(Value::Bool(true)))
        }

        "ToString" => {
            check_arity(name, args, 1, span)?;
            let val = eval(ctx, &args[0])?;
            // Use interning to enable pointer-based equality for repeated strings
            Ok(Some(Value::String(intern_string(&format!("{val}")))))
        }

        // d :> e - create single-element function [d |-> e]
        ":>" => {
            check_arity(name, args, 2, span)?;
            let domain_elem = eval(ctx, &args[0])?;
            let range_elem = eval(ctx, &args[1])?;
            // Create single-element function directly, avoiding im::OrdSet/OrdMap overhead
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                vec![(domain_elem, range_elem)],
            )))))
        }

        // f @@ g - merge two functions (f takes priority for overlapping domains)
        "@@" => {
            check_arity(name, args, 2, span)?;
            let fv = eval(ctx, &args[0])?;
            let gv = eval(ctx, &args[1])?;
            match (&fv, &gv) {
                (Value::Record(f), Value::Record(g)) => {
                    // Preserve record values for record field access syntax (r.field).
                    // f @@ g means f overrides g for overlapping keys (TLC semantics)
                    let mut merged = g.clone();
                    for (k, v) in f.iter() {
                        merged = merged.update(k, v.clone());
                    }
                    Ok(Some(Value::Record(merged)))
                }
                _ => {
                    let f = fv.to_func_coerced().ok_or_else(|| {
                        EvalError::type_error("Function", &fv, Some(args[0].span))
                    })?;
                    let g = gv.to_func_coerced().ok_or_else(|| {
                        EvalError::type_error("Function", &gv, Some(args[1].span))
                    })?;

                    // Merge: union of domains, f takes priority for overlapping keys
                    // Build combined entries: all of f, plus any from g not in f's domain
                    let mut entries: Vec<(Value, Value)> = f
                        .iter()
                        .map(|(key, value)| (key.clone(), value.clone()))
                        .collect();

                    // Add mappings from g that are not in f's domain
                    for (k, v) in g.mapping_iter() {
                        if !f.domain_contains(k) {
                            entries.push((k.clone(), v.clone()));
                        }
                    }

                    // Sort entries by key to maintain FuncValue invariant
                    entries.sort_by(|a, b| a.0.cmp(&b.0));

                    Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                        entries,
                    )))))
                }
            }
        }

        "SortSeq" => {
            // SortSeq(s, Op) - sort sequence using a comparator operator
            // Op(a, b) should return TRUE if a should come before b
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let seq = sv
                .as_seq()
                .ok_or_else(|| EvalError::type_error("Seq", &sv, Some(args[0].span)))?;

            // Comparator can be a user-defined operator name (Ident) or a built-in operator
            // reference (OpRef) like <, <=, etc.
            let cmp_op = match &args[1].node {
                Expr::Ident(name, _) => OperatorRef::UserDefined(name.clone()),
                Expr::OpRef(op) => OperatorRef::BuiltIn(op.clone()),
                _ => {
                    return Err(EvalError::Internal {
                        message: "SortSeq requires an operator as second argument".into(),
                        span,
                    });
                }
            };

            // Clone the sequence and sort it
            let mut result: Vec<Value> = seq.to_vec();

            // Use a simple insertion sort to avoid closure issues
            // (Rust's sort_by requires FnMut but we need to evaluate in ctx)
            for i in 1..result.len() {
                let mut j = i;
                while j > 0 {
                    // Compare result[j-1] with result[j]
                    let cmp_result = apply_binary_op(
                        ctx,
                        &cmp_op,
                        result[j - 1].clone(),
                        result[j].clone(),
                        span,
                    )?;
                    let a_before_b = cmp_result
                        .as_bool()
                        .ok_or_else(|| EvalError::type_error("BOOLEAN", &cmp_result, span))?;
                    if a_before_b {
                        break; // result[j-1] should come before result[j], no swap needed
                    }
                    result.swap(j - 1, j);
                    j -= 1;
                }
            }

            Ok(Some(Value::Seq(Arc::new(result.into()))))
        }

        "Permutations" => {
            // Permutations(S) - set of all permutation functions on set S
            // TLC semantics: returns a set of bijections [S -> S]
            // For {a, b}: returns {[a |-> a, b |-> b], [a |-> b, b |-> a]}
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let elements: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            let n = elements.len();

            // Guard against combinatorial explosion (n! grows fast)
            if n > 10 {
                return Err(EvalError::Internal {
                    message: format!(
                        "Permutations of {n} elements would be too large ({n}! permutations)"
                    ),
                    span,
                });
            }

            // Generate all permutation functions
            let mut perms = Vec::new();
            generate_permutation_functions(&elements, &[], &mut perms);
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(perms)))))
        }

        // JavaTime - returns current wall clock time in seconds since epoch
        "JavaTime" => {
            check_arity(name, args, 0, span)?;
            use std::time::{SystemTime, UNIX_EPOCH};
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0);
            // Zero MSB to prevent negative values (same as TLC)
            Ok(Some(Value::int(now & 0x7FFFFFFF)))
        }

        // TLCGet(x) - get TLC register or config (delegated to builtin_tlc_get)
        "TLCGet" => {
            check_arity(name, args, 1, span)?;
            eval_tlcget(ctx, args, span)
        }

        // TLCSet(i, v) - set TLC register (delegated to builtin_tlc_get)
        "TLCSet" => {
            check_arity(name, args, 2, span)?;
            eval_tlcset(ctx, args, span)
        }

        // RandomElement(S) - return a pseudo-random element from set S
        // Uses the fingerprint of S combined with a base seed to determine which element
        // to return. This ensures referential transparency: RandomElement(S) always returns
        // the same element for the same set S within a model checking run, but different
        // sets get different elements selected.
        //
        // This approach matches how TLC uses RandomElement in practice - for generating
        // varied but reproducible test cases. The "random" selection comes from mixing
        // the set's fingerprint with a global seed.
        "RandomElement" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            // Part of #2987: use TLC-normalized order so index selection matches TLC.
            let iter = eval_iter_set_tlc_normalized(ctx, &sv, Some(args[0].span))?;

            // Collect elements to allow random indexing
            let elements: Vec<Value> = iter.collect();
            if elements.is_empty() {
                return Err(EvalError::Internal {
                    message: "RandomElement requires non-empty set".into(),
                    span,
                });
            }

            if let Some(idx) = ctx.next_simulation_random_index(elements.len()) {
                crate::cache::dep_tracking::mark_runtime_nondeterministic(ctx);
                return Ok(Some(elements[idx].clone()));
            }

            // Use the set's fingerprint to deterministically select an element.
            // This ensures RandomElement(S) = RandomElement(S) for the same S,
            // while still providing varied selection across different sets.
            let fp = value_fingerprint(&sv).map_err(|e| EvalError::Internal {
                message: e.to_string(),
                span,
            })?;
            // Mix fingerprint with base seed for better distribution
            let idx = {
                let base = crate::eval_debug::random_base_seed();
                let mixed = fp.wrapping_mul(6364136223846793005).wrapping_add(base);
                (mixed % (elements.len() as u64)) as usize
            };
            Ok(Some(elements[idx].clone()))
        }

        // TLCEval(v) - force evaluation of lazy value (noop - TLA2 is already eager)
        "TLCEval" => {
            check_arity(name, args, 1, span)?;
            Ok(Some(eval(ctx, &args[0])?))
        }

        // Any / ANY - the set of all values (infinite, non-enumerable)
        // TLC provides this via TLC!Any and the AnySet module.
        "Any" | "ANY" => {
            check_arity(name, args, 0, span)?;
            Ok(Some(Value::AnySet))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
