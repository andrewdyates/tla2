// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Evaluator helpers: arithmetic, set semantics, operator application, quantifiers,
//! builtin dispatch, function values, and module references.
//!
//! Split into focused sub-modules as part of #1669.

pub(crate) mod apply;
mod bound_bindings;
mod bound_var_ops;
mod builtin_dispatch;
mod captured_restore;
mod closures;
pub(crate) mod function_values;
mod lazy_func_materialize;
mod module_ref;
pub(crate) mod module_ref_cache;
mod module_ref_chained;
mod module_ref_chained_label;
mod module_ref_instance;
mod module_ref_label;
mod module_ref_operator;
mod param_cache;
pub(crate) mod quantifiers;
mod recursive_fold;
mod set_construction;
mod set_semantics;

// === Re-exports: public API (used outside tla-eval crate) ===
pub use self::builtin_dispatch::has_complete_builtin_override;
pub use self::lazy_func_materialize::materialize_lazy_func_to_func;
pub use self::module_ref::{
    apply_substitutions, clear_eager_bindings_cache, clear_module_ref_caches,
    compose_substitutions, evict_next_state_eager_bindings, expr_has_any_prime,
    expr_has_primed_param, trim_module_ref_caches,
};
pub(crate) use self::param_cache::clear_param_name_caches;
// Part of #3962: clear_fold_cache removed — fold_result_cache consolidated into SMALL_CACHES.
pub use self::quantifiers::push_bound_var_mut;
pub use self::set_semantics::{
    eval_iter_set, eval_iter_set_tlc_normalized, materialize_setpred_to_vec, values_equal,
};
// Part of #3978: Streaming SetPred iteration and cardinality counting.
pub(crate) use self::set_semantics::count_setpred_streaming;
pub(crate) use self::set_semantics::try_stream_setpred;

// === Re-exports: crate-internal API (used by sibling modules in tla-eval/src/) ===
pub(super) use self::apply::{apply_closure_with_values, apply_user_op_with_values, eval_apply};
pub(crate) use self::bound_var_ops::{is_simple_tir_bound, push_tir_bound_var};
pub(super) use self::builtin_dispatch::{
    check_arity, eval_builtin, generate_permutation_functions, should_prefer_builtin_override,
};
pub(crate) use self::captured_restore::restore_captured_binding_chain;
pub(super) use self::closures::{build_lazy_func_from_ctx, create_closure_from_arg};
pub(super) use self::function_values::{
    eval_except, eval_func_apply, eval_func_def, try_borrow_materialized_read,
};
pub(super) use self::module_ref::{build_lazy_subst_bindings, eval_module_ref_target};
pub(super) use self::quantifiers::{
    eval_choose, eval_exists, eval_forall, into_bind_local_bound_var,
    into_bind_local_bound_var_cached, push_bound_var_mut_preinterned, PreInternedBound,
};
pub(crate) use self::quantifiers::{eval_choose_single, eval_quantifier_single};
pub(super) use self::set_construction::{
    count_set_filter_elements, eval_set_builder, eval_set_filter,
};

// === Re-exports: used by helpers sub-modules (function_values.rs needs these via `use super::*`) ===
// These maintain backward compatibility so existing sub-modules don't need import changes.
use self::closures::build_lazy_func_ctx;

// === Imports for remaining helper functions in this file ===
use super::{
    eval, int_arith_op, int_div_op, int_mod_op, int_pow_op, EvalCtx, EvalError, EvalResult,
};
use crate::value::{FuncValue, Value};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use tla_core::ast::Expr;
use tla_core::{Span, Spanned};

// === Interval length helper ===
// Part of #2013: checked arithmetic to avoid i64 overflow in debug mode.

/// Compute the length of an integer interval `[min, max]` for bounds checking.
///
/// Delegates to [`tla_value::checked_interval_len`]. Returns `0` for inverted
/// intervals (`max < min`). Returns `usize::MAX` on arithmetic overflow
/// (e.g., `[i64::MIN, i64::MAX]`), which safely fails subsequent bounds checks.
#[inline]
pub fn interval_len_for_bounds_check(min: i64, max: i64) -> usize {
    tla_value::checked_interval_len(min, max).unwrap_or(usize::MAX)
}

// === Sequence-like length helpers ===
// Shared by eval_arith.rs (\o binary op) and builtin_sequences.rs (\o / \circ builtin).

/// Check if a FuncValue represents a valid sequence (keys are 1..n) and return its length.
pub(super) fn func_seq_len(f: &FuncValue) -> Option<usize> {
    let mut expected: i64 = 1;
    for key in f.domain_iter() {
        if key.as_i64()? != expected {
            return None;
        }
        expected += 1;
    }
    Some((expected - 1) as usize)
}

/// Get the length of a sequence-like value (Seq, Tuple, IntFunc with min=1, or Func with 1..n keys).
pub(super) fn seq_like_len(v: &Value) -> Option<usize> {
    if let Some(elems) = v.as_seq_or_tuple_elements() {
        return Some(elems.len());
    }
    match v {
        Value::IntFunc(f) if tla_value::IntIntervalFunc::min(f) == 1 => Some(f.len()),
        Value::Func(f) => func_seq_len(f),
        _ => None,
    }
}

// === DyadicRationals helpers ===

/// Create a dyadic rational record [num |-> n, den |-> d]
pub(super) fn make_dyadic_rational(num: i64, den: i64) -> Value {
    let fields = vec![
        ("num".to_string(), Value::int(num)),
        ("den".to_string(), Value::int(den)),
    ];
    Value::Record(fields.into())
}

/// Extract numerator and denominator from a dyadic rational record
pub(super) fn extract_dyadic(v: &Value, span: Option<Span>) -> EvalResult<(i64, i64)> {
    if let Some(rec) = v.as_record() {
        let num = rec
            .get("num")
            .and_then(tla_value::Value::to_bigint)
            .and_then(|n| n.to_i64())
            .ok_or_else(|| EvalError::Internal {
                message: "DyadicRational requires 'num' field as integer".into(),
                span,
            })?;
        let den = rec
            .get("den")
            .and_then(tla_value::Value::to_bigint)
            .and_then(|n| n.to_i64())
            .ok_or_else(|| EvalError::Internal {
                message: "DyadicRational requires 'den' field as integer".into(),
                span,
            })?;
        Ok((num, den))
    } else {
        Err(EvalError::Internal {
            message: format!("Expected DyadicRational record, got {v:?}"),
            span,
        })
    }
}

/// GCD using Euclidean algorithm
pub(super) fn gcd(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Reduce a fraction to lowest terms
pub(super) fn reduce_fraction(num: i64, den: i64) -> (i64, i64) {
    if num == 0 {
        return (0, 1);
    }
    let g = gcd(num, den);
    (num / g, den / g)
}

// === Arithmetic evaluation helpers ===

/// Evaluate binary arithmetic expression with SmallInt fast path.
/// Part of #2955: inline hot-path arithmetic (Sum accumulation).
#[inline(always)]
pub(super) fn eval_arith(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    small_op: impl Fn(i64, i64) -> Option<i64>,
    big_op: impl Fn(BigInt, BigInt) -> BigInt,
    op_name: &str,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    int_arith_op(av, bv, small_op, big_op, op_name, Some(a.span))
}

/// Evaluate division expression with SmallInt fast path and zero check
pub(super) fn eval_div(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    small_op: impl Fn(i64, i64) -> Option<i64>,
    big_op: impl Fn(BigInt, BigInt) -> BigInt,
    op_name: &str,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    int_div_op(av, bv, small_op, big_op, op_name, span)
}

/// Evaluate modulus expression with TLC-compatible positive divisor check
pub(super) fn eval_mod(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    int_mod_op(av, bv, span)
}

/// Evaluate power expression with SmallInt fast path
pub(super) fn eval_pow(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    int_pow_op(av, bv, span)
}

pub(super) fn eval_comparison(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    cmp: impl Fn(std::cmp::Ordering) -> bool,
    op_name: &str,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    // SmallInt fast path: compare i64 directly without BigInt allocation
    if let (Value::SmallInt(an), Value::SmallInt(bn)) = (&av, &bv) {
        return Ok(Value::Bool(cmp(an.cmp(bn))));
    }
    // TLC: EC.TLC_MODULE_ARGUMENT_ERROR
    let an = av
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("first", op_name, "integer", &av, Some(a.span)))?;
    let bn = bv.to_bigint().ok_or_else(|| {
        EvalError::argument_error("second", op_name, "integer", &bv, Some(b.span))
    })?;
    Ok(Value::Bool(cmp(an.cmp(&bn))))
}

#[cfg(test)]
mod tests {
    use super::interval_len_for_bounds_check;
    use crate::cache::{clear_quantifier_hoist_cache, is_hoist_active};
    use tla_core::ast::{BoundVar, Expr, Unit};
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    fn with_forall_bounds_and_body<T>(src: &str, f: impl FnOnce(&[BoundVar], &Expr) -> T) -> T {
        let module_src = format!("---- MODULE Test ----\n\nOp == {}\n\n====", src);
        let tree = parse_to_syntax_tree(&module_src);
        let lower_result = lower(FileId(0), &tree);
        assert!(
            lower_result.errors.is_empty(),
            "lower errors: {:?}",
            lower_result.errors
        );
        let module = lower_result.module.expect("Op module should lower");

        for unit in &module.units {
            if let Unit::Operator(def) = &unit.node {
                if def.name.node == "Op" {
                    if let Expr::Forall(bounds, body) = &def.body.node {
                        return f(bounds, &body.node);
                    }
                    panic!("Op should lower to a forall expression");
                }
            }
        }

        panic!("Op definition not found");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_len_for_bounds_check_overflow_guard() {
        // Normal case
        assert_eq!(interval_len_for_bounds_check(1, 3), 3);
        // Inverted intervals (max < min) are empty → length 0
        assert_eq!(interval_len_for_bounds_check(2, 1), 0);
        assert_eq!(interval_len_for_bounds_check(100, 0), 0);
        // Overflow case: i64::MAX - 0 + 1 overflows i64, returns usize::MAX
        assert_eq!(interval_len_for_bounds_check(0, i64::MAX), usize::MAX);
        // Full range: i64::MAX - i64::MIN overflows i64, returns usize::MAX
        assert_eq!(
            interval_len_for_bounds_check(i64::MIN, i64::MAX),
            usize::MAX
        );
        // Single element
        assert_eq!(interval_len_for_bounds_check(5, 5), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_quantifier_hoist_scope_disabled() {
        // Part of #3128: Hoisting disabled due to correctness bug in nested
        // quantifier interaction (SlidingPuzzles ChooseOne). TLC has zero
        // quantifier hoisting — this matches TLC behavior.
        clear_quantifier_hoist_cache();
        assert!(
            !is_hoist_active(),
            "test must start without a leaked hoist frame"
        );

        with_forall_bounds_and_body(
            r#"\A x \in {1, 2, 3} : x \in ({1} \cup {2} \cup {3})"#,
            |bounds, body| {
                let guard = super::quantifiers::enter_hoist_scope(body, bounds);
                assert!(
                    guard.is_none(),
                    "hoist scope must be disabled (HOIST_ENABLED=false)"
                );
                assert!(
                    !is_hoist_active(),
                    "hoist stack must remain inactive when HOIST_ENABLED=false"
                );
            },
        );

        clear_quantifier_hoist_cache();
    }
}
