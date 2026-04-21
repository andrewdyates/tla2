// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(super) use super::int_arith::{int_arith_op, int_cmp_op, int_div_op, int_mod_op, int_pow_op};
use super::{
    apply_closure_with_values, eval, eval_constructors::union_values, extract_dyadic,
    make_dyadic_rational, reduce_fraction, seq_like_len, should_prefer_builtin_override, EvalCtx,
    EvalError, EvalResult, Span, Value,
};
use crate::value::{intern_string, SetCapValue, SetDiffValue};
use num_integer::Integer;
use std::sync::Arc;
// Binary operations and arithmetic helpers for TLA+ evaluation.
// Extracted from core.rs as part of #1219 decomposition.

/// Reference to an operator (either user-defined or built-in)
#[derive(Debug, Clone)]
pub(super) enum OperatorRef {
    /// User-defined operator (looked up in ops)
    UserDefined(String),
    /// Built-in operator (+, -, *, etc.)
    BuiltIn(String),
}

/// Apply a binary operator (user-defined or built-in) to two values
pub(super) fn apply_binary_op(
    ctx: &EvalCtx,
    op_ref: &OperatorRef,
    left: Value,
    right: Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    match op_ref {
        OperatorRef::UserDefined(op_name) => {
            // Look up user-defined operator
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
            let new_ctx = ctx.bind2(
                op_def.params[0].name.node.as_str(),
                left,
                op_def.params[1].name.node.as_str(),
                right,
            );
            eval(&new_ctx, &op_def.body)
        }
        OperatorRef::BuiltIn(op) => {
            // Apply built-in operator directly
            apply_builtin_binary_op(op, left, right, span)
        }
    }
}

/// Apply a named binary operator to two pre-evaluated values.
/// Checks for closure bindings first, then mirrors the normal operator
/// dispatch order for user-defined ops, builtin overrides, and stdlib builtins.
/// This avoids the expensive closure machinery used in
/// create_closure_from_arg + apply_closure_with_values.
pub(super) fn apply_named_binary_op(
    ctx: &EvalCtx,
    op_name: &str,
    left: Value,
    right: Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Higher-order operator parameters are bound as closures in the local
    // environment. They must shadow stdlib/user-defined operator lookup.
    if let Some(Value::Closure(ref closure)) = ctx.lookup(op_name) {
        return apply_closure_with_values(ctx, closure, &[left, right], span);
    }

    let resolved_name = ctx.resolve_op_name(op_name);

    if let Some(def) = ctx.get_op(resolved_name) {
        if should_prefer_builtin_override(resolved_name, def, 2, ctx)
            && is_stdlib_binary_op(resolved_name, ctx)
        {
            return apply_stdlib_binary_op(resolved_name, left, right, span);
        }

        if def.params.len() != 2 {
            return Err(EvalError::ArityMismatch {
                op: resolved_name.to_string(),
                expected: 2,
                got: def.params.len(),
                span,
            });
        }
        let new_ctx = ctx.bind2(
            def.params[0].name.node.as_str(),
            left,
            def.params[1].name.node.as_str(),
            right,
        );
        return eval(&new_ctx, &def.body);
    }

    // Fast path: use Rust builtins for stdlib operators when no user-defined
    // operator shadows them in the current scope.
    if is_stdlib_binary_op(resolved_name, ctx) {
        return apply_stdlib_binary_op(resolved_name, left, right, span);
    }

    Err(EvalError::UndefinedOp {
        name: resolved_name.to_string(),
        span,
    })
}

/// Check if a binary operator name has a stdlib builtin implementation.
/// Only matches when the source module (DyadicRationals) is actually imported.
pub(super) fn is_stdlib_binary_op(name: &str, ctx: &EvalCtx) -> bool {
    matches!(name, "Add") && ctx.shared.extended_module_names.contains("DyadicRationals")
}

/// Apply a stdlib binary builtin (e.g., DyadicRationals.Add) to pre-evaluated values.
/// This is the fast path that avoids creating closures or synthetic AST nodes.
pub(super) fn apply_stdlib_binary_op(
    op_name: &str,
    left: Value,
    right: Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    match op_name {
        "Add" => {
            // DyadicRationals.Add(p, q) with pre-evaluated values
            let (p_num, p_den) = extract_dyadic(&left, span)?;
            let (q_num, q_den) = extract_dyadic(&right, span)?;
            if p_num == 0 {
                return Ok(right);
            }
            let lcm = std::cmp::max(p_den, q_den);
            let p_scaled = p_num * (lcm / p_den);
            let q_scaled = q_num * (lcm / q_den);
            let sum_num = p_scaled + q_scaled;
            let (reduced_num, reduced_den) = reduce_fraction(sum_num, lcm);
            Ok(make_dyadic_rational(reduced_num, reduced_den))
        }
        _ => Err(EvalError::UndefinedOp {
            name: op_name.to_string(),
            span,
        }),
    }
}

/// Apply a built-in binary operator
pub(super) fn apply_builtin_binary_op(
    op: &str,
    left: Value,
    right: Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    match op {
        // Basic arithmetic - use int_arith_op helper
        "+" => int_arith_op(left, right, i64::checked_add, |a, b| a + b, "+", span),
        "-" => int_arith_op(left, right, i64::checked_sub, |a, b| a - b, "-", span),
        "*" => int_arith_op(left, right, i64::checked_mul, |a, b| a * b, "*", span),

        // Division operations - use int_div_op helper (includes zero check)
        "/" => int_div_op(left, right, i64::checked_div, |a, b| a / b, "/", span),
        "\\div" => int_div_op(
            left,
            right,
            |a, b| {
                if a == i64::MIN && b == -1 {
                    return None;
                }
                let q = a / b;
                if (a ^ b) < 0 && a % b != 0 {
                    Some(q - 1)
                } else {
                    Some(q)
                }
            },
            |a, b| a.div_floor(&b),
            "\\div",
            span,
        ),
        // Modulus - TLC requires positive divisor (y > 0)
        "%" => int_mod_op(left, right, span),

        // Power - use int_pow_op helper
        "^" => int_pow_op(left, right, span),

        // Comparisons (also used as operator arguments, e.g. SortSeq(s, <))
        "<" => int_cmp_op(left, right, |a, b| a < b, |a, b| a < b, "<", span),
        "\\leq" | "<=" => int_cmp_op(left, right, |a, b| a <= b, |a, b| a <= b, "\\leq", span),
        ">" => int_cmp_op(left, right, |a, b| a > b, |a, b| a > b, ">", span),
        "\\geq" | ">=" => int_cmp_op(left, right, |a, b| a >= b, |a, b| a >= b, "\\geq", span),

        "\\cup" => {
            // Fast path: single-element union (e.g., sent \cup {<<x, y>>})
            // Check if element already present before cloning
            if let Value::Set(ref b_set) = right {
                if b_set.len() == 1 {
                    if let Value::Set(ref a_set) = left {
                        let Some(elem) = b_set.iter().next() else {
                            return Err(EvalError::Internal {
                                message: "single-element set optimization expected one RHS element"
                                    .into(),
                                span,
                            });
                        };
                        // Short-circuit: if element already in set, return original unchanged
                        if a_set.contains(elem) {
                            return Ok(left.clone());
                        }
                        // Insert returns a new SortedSet
                        let result = a_set.insert(elem.clone());
                        return Ok(Value::from_sorted_set(result));
                    }
                }
            }
            // Symmetric fast path: {x} \cup larger_set
            if let Value::Set(ref a_set) = left {
                if a_set.len() == 1 {
                    if let Value::Set(ref b_set) = right {
                        let Some(elem) = a_set.iter().next() else {
                            return Err(EvalError::Internal {
                                message: "single-element set optimization expected one LHS element"
                                    .into(),
                                span,
                            });
                        };
                        // Short-circuit: if element already in set, return original unchanged
                        if b_set.contains(elem) {
                            return Ok(right.clone());
                        }
                        // Insert returns a new SortedSet
                        let result = b_set.insert(elem.clone());
                        return Ok(Value::from_sorted_set(result));
                    }
                }
            }
            // Type guard: reject non-set values before lazy fallback (#2269)
            if !left.is_set() {
                return Err(EvalError::type_error("Set", &left, span));
            }
            if !right.is_set() {
                return Err(EvalError::type_error("Set", &right, span));
            }
            union_values(left, right, span, span)
        }
        "\\cap" => {
            // Fast path: single-element intersection (e.g., {x} \cap S)
            // Result is either {x} if x in S, or {} otherwise
            if let Value::Set(ref a_set) = left {
                if a_set.len() == 1 {
                    if let Value::Set(ref b_set) = right {
                        // Check if the single element is in the other set
                        let Some(elem) = a_set.iter().next() else {
                            return Err(EvalError::Internal {
                                message:
                                    "single-element intersection optimization expected one LHS element"
                                        .into(),
                                span,
                            });
                        };
                        if b_set.contains(elem) {
                            return Ok(left.clone());
                        }
                        return Ok(Value::empty_set());
                    }
                }
            }
            // Symmetric fast path: S \cap {x}
            if let Value::Set(ref b_set) = right {
                if b_set.len() == 1 {
                    if let Value::Set(ref a_set) = left {
                        let Some(elem) = b_set.iter().next() else {
                            return Err(EvalError::Internal {
                                message:
                                    "single-element intersection optimization expected one RHS element"
                                        .into(),
                                span,
                            });
                        };
                        if a_set.contains(elem) {
                            return Ok(right.clone());
                        }
                        return Ok(Value::empty_set());
                    }
                }
            }
            // Type guard: reject non-set values before lazy fallback (#2269)
            if !left.is_set() {
                return Err(EvalError::type_error("Set", &left, span));
            }
            if !right.is_set() {
                return Err(EvalError::type_error("Set", &right, span));
            }
            match (left.to_sorted_set(), right.to_sorted_set()) {
                (Some(a), Some(b)) => Ok(Value::from_sorted_set(a.intersection(&b))),
                _ => Ok(Value::SetCap(SetCapValue::new(left, right))),
            }
        }
        "\\" => {
            // Fast path: single-element difference (e.g., Corr \ {self})
            // Check if element present before cloning
            if let Value::Set(ref b_set) = right {
                if b_set.len() == 1 {
                    if let Value::Set(ref a_set) = left {
                        let Some(elem) = b_set.iter().next() else {
                            return Err(EvalError::Internal {
                                message: "single-element difference optimization expected one RHS element"
                                    .into(),
                                span,
                            });
                        };
                        // Short-circuit: if element not in set, return original unchanged
                        if !a_set.contains(elem) {
                            return Ok(left.clone());
                        }
                        // Remove returns a new SortedSet
                        let result = a_set.remove(elem);
                        return Ok(Value::from_sorted_set(result));
                    }
                }
            }
            // Type guard: reject non-set values before lazy fallback (#2269)
            if !left.is_set() {
                return Err(EvalError::type_error("Set", &left, span));
            }
            if !right.is_set() {
                return Err(EvalError::type_error("Set", &right, span));
            }
            match (left.to_sorted_set(), right.to_sorted_set()) {
                (Some(a), Some(b)) => Ok(Value::from_sorted_set(a.difference(&b))),
                _ => Ok(Value::SetDiff(SetDiffValue::new(left, right))),
            }
        }
        "\\o" => {
            // String concatenation: "abc" \o "def" = "abcdef"
            // TLC parity: StringValue \o StringValue → string (Sequences.java:147-158)
            if let Value::String(s1) = &left {
                if let Value::String(s2) = &right {
                    // Part of #3287: Route through intern_string() so the TLC
                    // string token is assigned at creation time, not at first
                    // comparison via tlc_cmp().
                    return Ok(Value::String(intern_string(&format!("{}{}", &**s1, &**s2))));
                }
                return Err(EvalError::evaluating_error(
                    "t \\o s", "string", &right, span,
                ));
            }
            // Sequence concatenation (uses shared seq_like_len from helpers.rs)
            // TLC: EC.TLC_MODULE_EVALUATING with "s \\o t" for first arg, "t \\o s" for second
            let a_len = seq_like_len(&left)
                .ok_or_else(|| EvalError::evaluating_error("s \\o t", "sequence", &left, span))?;
            let b_len = seq_like_len(&right)
                .ok_or_else(|| EvalError::evaluating_error("t \\o s", "sequence", &right, span))?;

            let mut result: Vec<Value> = Vec::with_capacity(a_len + b_len);

            if let Some(elems) = left.as_seq_or_tuple_elements() {
                result.extend(elems.iter().cloned());
            } else {
                match &left {
                    Value::IntFunc(f) if tla_value::IntIntervalFunc::min(f) == 1 => {
                        result.extend(f.values().iter().cloned());
                    }
                    Value::Func(f) => {
                        let mut expected: i64 = 1;
                        for (k, v) in f.mapping_iter() {
                            let Some(idx) = k.as_i64() else {
                                return Err(EvalError::evaluating_error(
                                    "s \\o t", "sequence", &left, span,
                                ));
                            };
                            if idx != expected {
                                return Err(EvalError::evaluating_error(
                                    "s \\o t", "sequence", &left, span,
                                ));
                            }
                            expected += 1;
                            result.push(v.clone());
                        }
                    }
                    _ => {
                        return Err(EvalError::evaluating_error(
                            "s \\o t", "sequence", &left, span,
                        ));
                    }
                }
            }

            if let Some(elems) = right.as_seq_or_tuple_elements() {
                result.extend(elems.iter().cloned());
            } else {
                match &right {
                    Value::IntFunc(f) if tla_value::IntIntervalFunc::min(f) == 1 => {
                        result.extend(f.values().iter().cloned());
                    }
                    Value::Func(f) => {
                        let mut expected: i64 = 1;
                        for (k, v) in f.mapping_iter() {
                            let Some(idx) = k.as_i64() else {
                                return Err(EvalError::evaluating_error(
                                    "t \\o s", "sequence", &right, span,
                                ));
                            };
                            if idx != expected {
                                return Err(EvalError::evaluating_error(
                                    "t \\o s", "sequence", &right, span,
                                ));
                            }
                            expected += 1;
                            result.push(v.clone());
                        }
                    }
                    _ => {
                        return Err(EvalError::evaluating_error(
                            "t \\o s", "sequence", &right, span,
                        ));
                    }
                }
            }
            Ok(Value::Seq(Arc::new(result.into())))
        }
        _ => Err(EvalError::Internal {
            message: format!("Unknown built-in binary operator: {op}"),
            span,
        }),
    }
}
