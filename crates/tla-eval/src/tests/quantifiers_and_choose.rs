// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_if_then_else() {
    assert_eq!(eval_str("IF TRUE THEN 1 ELSE 2").unwrap(), Value::int(1));
    assert_eq!(eval_str("IF FALSE THEN 1 ELSE 2").unwrap(), Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_case() {
    assert_eq!(
        eval_str("CASE TRUE -> 1 [] FALSE -> 2").unwrap(),
        Value::int(1)
    );
    assert_eq!(
        eval_str("CASE FALSE -> 1 [] TRUE -> 2").unwrap(),
        Value::int(2)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_case_exhaustion_returns_case_no_match() {
    let err = eval_str("CASE FALSE -> 1 [] FALSE -> 2").unwrap_err();
    assert!(
        matches!(err, EvalError::CaseNoMatch { .. }),
        "#1754: CASE exhaustion should return CaseNoMatch, got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_let() {
    assert_eq!(eval_str("LET x == 5 IN x + 1").unwrap(), Value::int(6));
    assert_eq!(
        eval_str("LET a == 2 b == 3 IN a * b").unwrap(),
        Value::int(6)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_forall() {
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : x > 0"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : x > 2"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#"\A <<x, y>> \in {<<1, 2>>, <<3, 4>>} : x < y"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"\A <<x, y>> \in {<<1, 2>>, <<3, 4>>} : x + y = 3"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_subset_fast_path_preserves_empty_domain_vacuity() {
    assert_eq!(
        eval_str(r#"\A x \in {} : x \in 1"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_subset_fast_path_skips_bound_dependent_rhs() {
    assert_eq!(
        eval_str(r#"\A x \in {1, 2} : x \in {x}"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_subset_fast_path_handles_zero_arg_rhs_alias() {
    assert_eq!(
        eval_str(r#"LET Messages == {1} \cup {2} IN \A x \in {1, 2} : x \in Messages"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_exists() {
    assert_eq!(
        eval_str(r#"\E x \in {1, 2, 3} : x > 2"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"\E x \in {1, 2, 3} : x > 5"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_uses_tlc_normalized_order() {
    // EXISTS short-circuits on the first TRUE element.
    // TLC-normalized tuple order is length-first, so <<2>> precedes <<1, 1>>.
    assert_eq!(
        eval_str(
            r#"/\ (\E t \in {<<2>>, <<1, 1>>} : TLCSet(13, t))
               /\ TLCGet(13) = <<2>>"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_choose() {
    // CHOOSE returns the TLC-minimum element satisfying the predicate.
    // Must be exactly 2 (not 3) to verify deterministic TLC-normalized ordering.
    let v = eval_str(r#"CHOOSE x \in {1, 2, 3} : x > 1"#).unwrap();
    assert_eq!(v, Value::int(2));
    let tuple = eval_str(r#"CHOOSE <<x, y>> \in {<<1, 2>>, <<3, 4>>} : x + y = 7"#).unwrap();
    assert_eq!(tuple, Value::tuple([Value::int(3), Value::int(4)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_over_filtered_subset_domain() {
    // Regression test for #1814: if set-filter over SUBSET is represented lazily
    // (SetPred), CHOOSE must still enumerate/filter correctly.
    let result = eval_str(r#"CHOOSE s \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 3 \in s"#).unwrap();
    assert_eq!(result, Value::set([Value::int(2), Value::int(3)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifiers_over_filtered_subset_domain() {
    // Regression test for #1814: \A and \E over filtered SUBSET domains should
    // work even when the domain is represented as lazy SetPred.
    assert_eq!(
        eval_str(r#"\A s \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 2 \in s"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"\E s \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 1 \in s /\ 3 \in s"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_over_nested_filtered_subset_domain() {
    // Regression test for #1827: nested set-filters over SUBSET create
    // SetPred(source=SetPred). CHOOSE iteration must recurse through both.
    let result =
        eval_str(r#"CHOOSE s \in {u \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 3 \in u} : 1 \in s"#)
            .unwrap();
    assert_eq!(
        result,
        Value::set([Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifiers_over_nested_filtered_subset_domain() {
    assert_eq!(
        eval_str(r#"\A s \in {u \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 3 \in u} : 2 \in s"#)
            .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"\E s \in {u \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 3 \in u} : 1 \in s"#)
            .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_normalized_order_set_elements() {
    // TLC normalizes the domain and selects the first satisfying element in normalized order.
    // For sets-as-elements, normalized order compares cardinality first.
    let result = eval_str(r#"CHOOSE s \in {{2}, {1, 2}} : TRUE"#).unwrap();
    assert_eq!(result, Value::set([Value::int(2)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_normalized_order_tuple_elements() {
    // TLC's tuple ordering compares length first. Thus <<2>> < <<1,1>>.
    let result = eval_str(r#"CHOOSE t \in {<<2>>, <<1, 1>>} : TRUE"#).unwrap();
    assert_eq!(result, Value::tuple([Value::int(2)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_normalized_order_model_value_lt_int() {
    // TLC: untyped model values compare less than any non-model value.
    let result = eval_str(r#"CHOOSE x \in {TLCModelValue("m"), 0} : TRUE"#).unwrap();
    assert_eq!(result, Value::try_model_value("m").unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_normalized_order_model_values_use_tlc_unique_string_order() {
    // TLC compares model values by UniqueString token order (not lexicographic order).
    // For model values created during expression evaluation, this corresponds to first-seen order.
    //
    // Use names that are extremely unlikely to be pre-registered by other tests.
    let result = eval_str(
        r#"CHOOSE x \in {TLCModelValue("__choose_mv_order_986_first_9b8a__"), TLCModelValue("__choose_mv_order_986_second_9b8a__")} : TRUE"#,
    )
    .unwrap();
    assert_eq!(
        result,
        Value::try_model_value("__choose_mv_order_986_first_9b8a__").unwrap()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_normalized_order_subset_cardinality_first() {
    // TLC: SUBSET enumeration is cardinality-first (all 1-subsets before any 2-subset, etc.).
    let result = eval_str(r#"CHOOSE t \in SUBSET {1, 2, 3, 4} : t = {1, 2} \/ t = {3}"#).unwrap();
    assert_eq!(result, Value::set([Value::int(3)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_errors_on_incomparable_domain_elems() {
    // TLC fails when normalizing sets containing incomparable element types (e.g. int vs string).
    let result = eval_str(r#"CHOOSE x \in {1, "a"} : TRUE"#);
    assert!(
        matches!(result, Err(EvalError::Internal { .. })),
        "{result:?}"
    );
}

// ============================================================
// Quantifier subexpression regression tests (#3128, #3147)
// These assertions remain semantic guards even while the runtime hoist lane is disabled.
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_invariant_subexpr_forall() {
    // The set union {1} \cup {2} does not depend on x.
    // This must stay TRUE both with hoisting disabled and if the lane is re-enabled.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : x \in ({1} \cup {2} \cup {3})"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_invariant_subexpr_exists() {
    // {10, 20} \cup {30} is invariant in x.
    // This remains the semantic baseline if caching is later re-enabled.
    assert_eq!(
        eval_str(r#"\E x \in {10, 20, 30} : x \in ({10, 20} \cup {30})"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_dependent_subexpr_not_cached() {
    // x + 1 depends on x — must NOT be cached across iterations.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : x + 1 > x"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"\E x \in {1, 2, 3} : x + 1 = 4"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_mixed_invariant_and_dependent() {
    // In `x \in S \cup T`, `S \cup T` is invariant but the whole `\in` depends on x.
    // If hoisting is re-enabled, only the union may be cached across iterations.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : x \in ({1, 2} \cup {3})"#).unwrap(),
        Value::Bool(true)
    );
    // Add 4 to domain but not to the invariant set — should be false.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3, 4} : x \in ({1, 2} \cup {3})"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_nested_quantifier_inner_invariant() {
    // Inner quantifier: `\A y \in T : y > x` — `x` is free (from outer) but
    // `y > x` depends on y. If hoisting is re-enabled, the outer scope must
    // NOT cache `y > x`; only the inner scope may cache y-invariant pieces.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2} : \A y \in {3, 4} : y > x"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_shadowed_variable_not_confused() {
    // Inner quantifier binds `x` again — the inner `x` shadows the outer.
    // `x + 1` in the inner body depends on the inner x, not the outer.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2} : \E x \in {10, 20} : x > 5"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_let_invariant_subexpr() {
    // LET s == {1, 2, 3} — `s` is defined outside the quantifier body scope
    // but inside the body AST via LET. The LET body is invariant in x.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : LET s == {1, 2, 3} IN x \in s"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_let_local_operator_capturing_bound_var_not_cached() {
    // `f` closes over the quantifier-bound `x`, so `f = 1` must be re-evaluated
    // per iteration whenever caching is enabled. Reusing the first result
    // across iterations would incorrectly return TRUE.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2} : LET f == x IN f = 1"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_let_operator_param_not_cached_across_calls() {
    // `a` varies across calls to `F`, so `a = 1` must not be hoisted across
    // quantifier iterations via the surrounding cache frame if that lane returns.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2} : LET F(a) == a = 1 IN F(x)"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_recursive_let_function_capturing_outer_quantifier_not_cached() {
    // VoteProof's SafeAt uses this recursive LET shape, but the real #3148
    // false positive was a separate scope-id bug. This test guards only the
    // quantifier-hoist lane: if the cache is re-enabled, reusing the first
    // iteration's recursive result for later iterations would make the second
    // case disagree with its own `v = 1` expectation.
    assert_eq!(
        eval_str(
            r#"\A v \in {1, 2} :
                 LET SA[bb \in 0..2] ==
                         IF bb = 0 THEN v = 1 ELSE SA[bb - 1]
                 IN SA[2] = (v = 1)"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_choose_dependent_subexpr_not_cached_across_outer_quantifier() {
    // The CHOOSE body depends on the outer x, so the whole CHOOSE expression
    // must be recomputed for each iteration if the hoist lane is re-enabled,
    // instead of reusing the first result.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2} : (CHOOSE y \in {1, 2, 3} : y > x) = x + 1"#).unwrap(),
        Value::Bool(true)
    );
}

// ============================================================
// Deep CHOOSE cache correctness tests (Part of #3905)
//
// These tests exercise CHOOSE at binding_depth > 0 (inside quantifiers),
// where the deep cache (keyed by expr_ptr + domain_hash + bindings_hash)
// must correctly distinguish different binding contexts.
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_true_inside_quantifier() {
    // CHOOSE TRUE inside a quantifier uses the bindings_hash=0 fast path.
    // The domain changes with x, so each CHOOSE returns a different value.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : (CHOOSE y \in {x, x+1} : TRUE) = x"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_true_same_domain_inside_quantifier() {
    // CHOOSE TRUE with constant domain inside quantifier: same result every time.
    // The deep cache should hit for all iterations after the first.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3} : (CHOOSE y \in {10, 20, 30} : TRUE) = 10"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_predicate_depends_on_outer_binding() {
    // Predicate depends on outer quantifier variable x.
    // Deep cache must use different bindings_hash for each x value.
    // CHOOSE y \in {1,2,3,4,5} : y > x gives x+1 for x in {1,2,3,4}.
    assert_eq!(
        eval_str(r#"\A x \in {1, 2, 3, 4} : (CHOOSE y \in {1, 2, 3, 4, 5} : y > x) = x + 1"#)
            .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_nested_quantifiers() {
    // CHOOSE inside doubly-nested quantifiers. The CHOOSE depends on both
    // outer variables, so the deep cache must distinguish all (x, y) pairs.
    assert_eq!(
        eval_str(
            r#"\A x \in {1, 2} : \A y \in {10, 20} :
                (CHOOSE z \in {11, 12, 21, 22} : z = x + y) = x + y"#
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_repeated_same_context() {
    // Two references to the same CHOOSE expression within one quantifier body.
    // Both should produce the same result (cache hit on second reference).
    assert_eq!(
        eval_str(
            r#"\A x \in {1, 2, 3} :
                LET c == CHOOSE y \in {x, x+1, x+2} : y > x
                IN c = c"#
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_operator_param_context() {
    // CHOOSE inside an operator with parameter — the parameter binding
    // must be captured in bindings_hash.
    assert_eq!(
        eval_str(
            r#"LET F(x) == CHOOSE y \in {1, 2, 3, 4, 5} : y > x
               IN F(1) = 2 /\ F(2) = 3 /\ F(3) = 4"#
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deep_choose_domain_varies_predicate_constant() {
    // Domain changes with outer variable, predicate is constant (not TRUE).
    // Deep cache distinguishes via domain_hash.
    assert_eq!(
        eval_str(
            r#"\A x \in {1, 2, 3} :
                (CHOOSE y \in {x*10, x*10+1, x*10+2} : y > x*10) = x*10 + 1"#
        )
        .unwrap(),
        Value::Bool(true)
    );
}
