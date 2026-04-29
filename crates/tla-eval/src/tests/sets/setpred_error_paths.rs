// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// === #1805 regression tests: NotInDomain propagation in SetPred paths ===

/// Regression test for #1805: materialization of SetPred must propagate
/// eval errors when the predicate accesses a function outside its domain.
/// Previously silently treated as false (element excluded from result).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_materialization_propagates_eval_error() {
    // {x \in {1,2,3} : f[x]} where f = [y \in {1,2} |-> TRUE]
    // When x=3, f[3] is out of bounds — must propagate, not silently exclude.
    let src = r#"LET f == [y \in {1,2} |-> TRUE]
                 IN {x \in {1,2,3} : f[x]}"#;
    let err = eval_str(src).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::NotInDomain { .. } | EvalError::IndexOutOfBounds { .. }
        ),
        "#1805: eval error in SetPred predicate must propagate during materialization, got: {:?}",
        err
    );
}

/// Regression test for #1805: Cardinality over SetPred must propagate
/// eval errors from predicate evaluation (exercises count_set_filter_elements).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_cardinality_propagates_eval_error() {
    let src = r#"LET f == [y \in {1,2} |-> TRUE]
                 IN Cardinality({x \in {1,2,3} : f[x]})"#;
    let err = eval_str(src).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::NotInDomain { .. } | EvalError::IndexOutOfBounds { .. }
        ),
        "#1805: eval error in SetPred predicate must propagate through Cardinality, got: {:?}",
        err
    );
}

/// Regression test for #1805: nonempty set check over SetPred must propagate
/// eval errors from predicate evaluation when the first element triggers the
/// error (exercises eval_is_nonempty_set).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_nonempty_check_propagates_eval_error() {
    // Use a domain where ALL elements trigger the error so the nonempty
    // check can't short-circuit by finding a match.
    let src = r#"LET f == [y \in {10,20} |-> TRUE]
                 IN {x \in {1,2,3} : f[x]} /= {}"#;
    let err = eval_str(src).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::NotInDomain { .. } | EvalError::IndexOutOfBounds { .. }
        ),
        "#1805: eval error in SetPred predicate must propagate through nonempty check, got: {:?}",
        err
    );
}

/// Regression test for b3cf3ad (Part of #2834): SetPred tuple destructuring in lazy
/// materialization. Both `materialize_setpred_to_vec` and the inner `materialize_setpred`
/// in `values_equal` must use `into_bind_local_bound_var` (which handles BoundPattern::Tuple)
/// instead of `bind_local` with the synthetic name "<<x, y>>".
///
/// Uses a cross-product domain (S \X T) which produces Value::Set (not Value::Subset),
/// but with a state-dependent predicate to force lazy SetPred creation when the predicate
/// references a state variable.
///
/// Before the fix, `{<<a, b>> \in {1,2} \X {3,4} : a + b > x}` would fail with
/// "Undefined variable: a" because `bind_local("<<a, b>>", <<1, 3>>)` doesn't
/// destructure the tuple pattern.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_materialize_setpred_tuple_destructuring() {
    clear_for_test_reset();

    // The cross-product domain {1,2} \X {3,4} combined with a state-dependent predicate
    // forces the lazy SetPred path. The BoundPattern::Tuple(<<a, b>>) must be destructured.
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Filtered == {<<a, b>> \in {1, 2} \X {3, 4} : a + b > x}
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // Evaluate with x = 4: only pairs where a + b > 4
    // {1,2} \X {3,4} = {<<1,3>>, <<1,4>>, <<2,3>>, <<2,4>>}
    // a+b > 4: <<1,4>> (5), <<2,3>> (5), <<2,4>> (6) → 3 elements
    let state = vec![Value::int(4)];
    ctx.bind_state_array(&state);
    let val = ctx.eval_op("Filtered");

    match val {
        Ok(ref v) => {
            // Should be a SetPred because predicate references state variable `x`
            if let Value::SetPred(ref spv) = v {
                let materialized = materialize_setpred_to_vec(&ctx, spv).unwrap();
                assert_eq!(
                    materialized.len(),
                    3,
                    "Tuple destructuring in SetPred should produce 3 elements where a+b > 4, \
                     got {:?}",
                    materialized
                );
            } else {
                // If eagerly evaluated, check the result directly
                let elems = v.iter_set().expect("should be iterable");
                let count = elems.count();
                assert_eq!(
                    count, 3,
                    "Tuple destructuring in SetPred should produce 3 elements where a+b > 4"
                );
            }
        }
        Err(e) => {
            panic!(
                "b3cf3ad regression: SetPred with tuple pattern <<a, b>> should not error. \
                 Before the fix, this failed with 'Undefined variable: a' because bind_local \
                 bound the synthetic name '<<a, b>>' instead of destructuring. Error: {e:?}"
            );
        }
    }
}

/// Regression test for b3cf3ad: values_equal path for SetPred with tuple destructuring.
///
/// Tests the inner `materialize_setpred` in `values_equal` (distinct from the public
/// `materialize_setpred_to_vec`). When comparing a lazy SetPred that uses tuple binding
/// against an explicit set, the values_equal materializer must also destructure the tuple.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_values_equal_tuple_destructuring() {
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Filtered == {<<a, b>> \in {1, 2} \X {3, 4} : a + b > x}
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // With x = 4: {<<1,4>>, <<2,3>>, <<2,4>>}
    let state = vec![Value::int(4)];
    ctx.bind_state_array(&state);
    let setpred_val = ctx.eval_op("Filtered");

    match setpred_val {
        Ok(ref v) => {
            let expected = Value::set([
                Value::tuple(vec![Value::int(1), Value::int(4)]),
                Value::tuple(vec![Value::int(2), Value::int(3)]),
                Value::tuple(vec![Value::int(2), Value::int(4)]),
            ]);
            let eq = values_equal(&ctx, v, &expected, None).unwrap();
            assert!(
                eq,
                "b3cf3ad regression: SetPred with tuple pattern should equal the expected set. \
                 Before the fix, this would fail with 'Undefined variable' during materialization."
            );
        }
        Err(e) => {
            panic!("b3cf3ad regression: SetPred with tuple destructuring should not error: {e:?}");
        }
    }
}
