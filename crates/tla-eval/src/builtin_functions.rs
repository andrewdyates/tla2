// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, FuncValue, SortedSet,
    Span, Spanned, Value,
};
use std::sync::Arc;
// Built-in Functions module operators (Restrict, IsInjective, Injection, Surjection, Bijection, etc.)

pub(super) fn eval_builtin_functions(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === Functions module ===
        "Restrict" => {
            // Restrict(f, S) - restrict domain of function f to elements in set S
            // Restrict(f, S) == [x \in S |-> f[x]]
            check_arity(name, args, 2, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Function", &fv, Some(args[0].span)))?;
            let sv = eval(ctx, &args[1])?;
            // Phase 1A (#3073): HashSet for O(1) membership lookup instead of OrdSet O(log n)
            // Part of #4112: FxHashSet for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let set: rustc_hash::FxHashSet<Value> =
                eval_iter_set(ctx, &sv, Some(args[1].span))?.collect();

            // Filter entries to those whose keys are in the set
            let entries: Vec<(Value, Value)> = func
                .mapping_iter()
                .filter(|(k, _)| set.contains(k))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();

            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        "IsInjective" => {
            // IsInjective(f) - TRUE if f is injective (one-to-one)
            // IsInjective(f) == \A a, b \in DOMAIN f: f[a] = f[b] => a = b
            check_arity(name, args, 1, span)?;
            let fv = eval(ctx, &args[0])?;
            // Allow: Value contains OnceLock for fingerprint caching, but Hash/Eq are stable
            // Part of #4112: FxHashSet for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let mut seen: rustc_hash::FxHashSet<Value> = rustc_hash::FxHashSet::default();

            match &fv {
                Value::Func(func) => {
                    for val in func.mapping_values() {
                        if !seen.insert(val.clone()) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                }
                Value::IntFunc(func) => {
                    for val in func.values() {
                        if !seen.insert(val.clone()) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                }
                Value::Seq(seq) => {
                    for val in seq.iter() {
                        if !seen.insert(val.clone()) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                }
                Value::Tuple(seq) => {
                    for val in seq.iter() {
                        if !seen.insert(val.clone()) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                }
                Value::Record(rec) => {
                    for (_k, val) in rec.iter() {
                        if !seen.insert(val.clone()) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                }
                _ => {
                    return Err(EvalError::type_error("Function", &fv, Some(args[0].span)));
                }
            }

            Ok(Some(Value::Bool(true)))
        }

        "IsSurjective" => {
            // IsSurjective(f, S, T) - TRUE if f restricted to S maps onto T
            // IsSurjective(f, S, T) == \A t \in T: \E s \in S: f[s] = t
            check_arity(name, args, 3, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Function", &fv, Some(args[0].span)))?;
            let sv = eval(ctx, &args[1])?;
            // Phase 1A (#3073): HashSet for O(1) membership, Vec for iteration
            // Part of #4112: FxHashSet for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let source: rustc_hash::FxHashSet<Value> =
                eval_iter_set(ctx, &sv, Some(args[1].span))?.collect();
            let tv = eval(ctx, &args[2])?;
            let target: Vec<Value> = eval_iter_set(ctx, &tv, Some(args[2].span))?.collect();

            // Get range of f restricted to S
            #[allow(clippy::mutable_key_type)]
            let range: rustc_hash::FxHashSet<Value> = func
                .mapping_iter()
                .filter(|(k, _)| source.contains(k))
                .map(|(_, v)| v.clone())
                .collect();

            // Check if every element of T is in the range
            let is_surjective = target.iter().all(|t| range.contains(t));
            Ok(Some(Value::Bool(is_surjective)))
        }

        "IsBijection" => {
            // IsBijection(f, S, T) - TRUE if f is a bijection from S to T
            // IsBijection(f, S, T) == IsInjective(Restrict(f, S)) /\ IsSurjective(f, S, T)
            check_arity(name, args, 3, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Function", &fv, Some(args[0].span)))?;
            let sv = eval(ctx, &args[1])?;
            // Phase 1A (#3073): HashSet for O(1) membership, Vec for iteration
            // Part of #4112: FxHashSet for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let source: rustc_hash::FxHashSet<Value> =
                eval_iter_set(ctx, &sv, Some(args[1].span))?.collect();
            let tv = eval(ctx, &args[2])?;
            let target: Vec<Value> = eval_iter_set(ctx, &tv, Some(args[2].span))?.collect();

            // Get restricted function values
            let restricted: Vec<&Value> = func
                .mapping_iter()
                .filter(|(k, _)| source.contains(k))
                .map(|(_, v)| v)
                .collect();

            // Check injective: all values are unique
            let unique_count = restricted
                .iter()
                .collect::<rustc_hash::FxHashSet<_>>()
                .len();
            let is_injective = restricted.len() == unique_count;

            // Get range of restricted function
            #[allow(clippy::mutable_key_type)]
            let range: rustc_hash::FxHashSet<Value> = restricted.into_iter().cloned().collect();

            // Check surjective: every element of T is in the range
            let is_surjective = target.iter().all(|t| range.contains(t));

            Ok(Some(Value::Bool(is_injective && is_surjective)))
        }

        "Inverse" => {
            // Inverse(f, S, T) - inverse of function f from S to T
            // Only valid if f is a bijection from S to T
            // Inverse(f, S, T) == [t \in T |-> CHOOSE s \in S: f[s] = t]
            check_arity(name, args, 3, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Function", &fv, Some(args[0].span)))?;
            let sv = eval(ctx, &args[1])?;
            // Phase 1A (#3073): HashSet for O(1) membership, Vec for iteration
            // Part of #4112: FxHashSet for faster hashing on Value keys.
            #[allow(clippy::mutable_key_type)]
            let source: rustc_hash::FxHashSet<Value> =
                eval_iter_set(ctx, &sv, Some(args[1].span))?.collect();
            let tv = eval(ctx, &args[2])?;
            let target: Vec<Value> = eval_iter_set(ctx, &tv, Some(args[2].span))?.collect();

            // Build inverse mapping
            let mut inverse_entries: Vec<(Value, Value)> = Vec::new();

            for t in &target {
                // Find s \in S such that f[s] = t
                let s = func
                    .mapping_iter()
                    .find(|(k, v)| source.contains(k) && *v == t)
                    .map(|(k, _)| k.clone());

                if let Some(s) = s {
                    inverse_entries.push((t.clone(), s));
                }
            }

            // Sort entries by key to maintain FuncValue invariant
            inverse_entries.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                inverse_entries,
            )))))
        }

        "Injection" => {
            // Injection(S, T) - the set of all injective functions from S to T
            // Injection(S, T) == { f \in [S -> T] : IsInjective(f) }
            // An injection maps distinct domain elements to distinct range elements
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let mut source_elems: Vec<Value> =
                eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            source_elems.sort();
            let tv = eval(ctx, &args[1])?;
            let mut target_elems: Vec<Value> =
                eval_iter_set(ctx, &tv, Some(args[1].span))?.collect();
            target_elems.sort();

            // For injection to exist, |S| <= |T|
            if source_elems.len() > target_elems.len() {
                return Ok(Some(Value::empty_set()));
            }

            let mut injections = Vec::new();

            // Generate all injective mappings using permutations
            collect_injective_function_values(&source_elems, &target_elems, &mut injections);

            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(injections)))))
        }

        "Surjection" => {
            // Surjection(S, T) - the set of all surjective functions from S to T
            // Surjection(S, T) == { f \in [S -> T] : IsSurjective(f, S, T) }
            // A surjection covers every element in T at least once
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let mut source_elems: Vec<Value> =
                eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            source_elems.sort();
            let tv = eval(ctx, &args[1])?;
            let mut target_elems: Vec<Value> =
                eval_iter_set(ctx, &tv, Some(args[1].span))?.collect();
            target_elems.sort();

            // For surjection to exist, |S| >= |T|
            if source_elems.len() < target_elems.len() {
                return Ok(Some(Value::empty_set()));
            }

            // Generate all functions [S -> T] and filter to surjections
            // This is expensive but correct
            let mut surjections = Vec::new();

            collect_surjective_function_values(&source_elems, &target_elems, &mut surjections);

            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(
                surjections,
            )))))
        }

        "Bijection" => {
            // Bijection(S, T) - the set of all bijective functions from S to T
            // Bijection(S, T) == Injection(S, T) \cap Surjection(S, T)
            // A bijection is both injective and surjective; requires |S| = |T|
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let mut source_elems: Vec<Value> =
                eval_iter_set(ctx, &sv, Some(args[0].span))?.collect();
            source_elems.sort();
            let tv = eval(ctx, &args[1])?;
            let mut target_elems: Vec<Value> =
                eval_iter_set(ctx, &tv, Some(args[1].span))?.collect();
            target_elems.sort();

            // Bijection requires same cardinality
            if source_elems.len() != target_elems.len() {
                return Ok(Some(Value::empty_set()));
            }

            // Generate all permutations (bijections are permutations of target)
            let mut bijections = Vec::new();

            collect_injective_function_values(&source_elems, &target_elems, &mut bijections);

            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(bijections)))))
        }

        "ExistsInjection" => {
            // ExistsInjection(S, T) - TRUE iff there exists an injection from S to T
            // ExistsInjection(S, T) == Cardinality(S) <= Cardinality(T)
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let source_count = eval_iter_set(ctx, &sv, Some(args[0].span))?.count();
            let tv = eval(ctx, &args[1])?;
            let target_count = eval_iter_set(ctx, &tv, Some(args[1].span))?.count();

            Ok(Some(Value::Bool(source_count <= target_count)))
        }

        "ExistsSurjection" => {
            // ExistsSurjection(S, T) - TRUE iff there exists a surjection from S to T
            // ExistsSurjection(S, T) == Cardinality(S) >= Cardinality(T)
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let source_count = eval_iter_set(ctx, &sv, Some(args[0].span))?.count();
            let tv = eval(ctx, &args[1])?;
            let target_count = eval_iter_set(ctx, &tv, Some(args[1].span))?.count();

            Ok(Some(Value::Bool(source_count >= target_count)))
        }

        "ExistsBijection" => {
            // ExistsBijection(S, T) - TRUE iff there exists a bijection from S to T
            // ExistsBijection(S, T) == Cardinality(S) = Cardinality(T)
            check_arity(name, args, 2, span)?;
            let sv = eval(ctx, &args[0])?;
            let source_count = eval_iter_set(ctx, &sv, Some(args[0].span))?.count();
            let tv = eval(ctx, &args[1])?;
            let target_count = eval_iter_set(ctx, &tv, Some(args[1].span))?.count();

            Ok(Some(Value::Bool(source_count == target_count)))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}

fn build_sorted_func_value(source: &[Value], mapped_values: &[Value]) -> Value {
    debug_assert_eq!(source.len(), mapped_values.len());
    let entries = source
        .iter()
        .cloned()
        .zip(mapped_values.iter().cloned())
        .collect();
    Value::Func(Arc::new(FuncValue::from_sorted_entries(entries)))
}

fn collect_injective_function_values(source: &[Value], target: &[Value], output: &mut Vec<Value>) {
    fn recurse(
        source: &[Value],
        target: &[Value],
        src_idx: usize,
        used: &mut [bool],
        current_values: &mut Vec<Value>,
        output: &mut Vec<Value>,
    ) {
        if src_idx == source.len() {
            output.push(build_sorted_func_value(source, current_values));
            return;
        }

        for (t_idx, target_value) in target.iter().enumerate() {
            if used[t_idx] {
                continue;
            }
            used[t_idx] = true;
            current_values.push(target_value.clone());
            recurse(source, target, src_idx + 1, used, current_values, output);
            current_values.pop();
            used[t_idx] = false;
        }
    }

    let mut used = vec![false; target.len()];
    let mut current_values = Vec::with_capacity(source.len());
    recurse(source, target, 0, &mut used, &mut current_values, output);
}

fn collect_surjective_function_values(source: &[Value], target: &[Value], output: &mut Vec<Value>) {
    fn recurse(
        source: &[Value],
        target: &[Value],
        src_idx: usize,
        current_values: &mut Vec<Value>,
        target_hits: &mut [usize],
        covered_targets: usize,
        output: &mut Vec<Value>,
    ) {
        if src_idx == source.len() {
            if covered_targets == target.len() {
                output.push(build_sorted_func_value(source, current_values));
            }
            return;
        }

        for (t_idx, target_value) in target.iter().enumerate() {
            current_values.push(target_value.clone());
            let was_uncovered = target_hits[t_idx] == 0;
            target_hits[t_idx] += 1;
            let next_covered = covered_targets + usize::from(was_uncovered);

            recurse(
                source,
                target,
                src_idx + 1,
                current_values,
                target_hits,
                next_covered,
                output,
            );

            target_hits[t_idx] -= 1;
            current_values.pop();
        }
    }

    let mut current_values = Vec::with_capacity(source.len());
    let mut target_hits = vec![0usize; target.len()];
    recurse(
        source,
        target,
        0,
        &mut current_values,
        &mut target_hits,
        0,
        output,
    );
}
