// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// === #1814 regression tests: Cardinality over SetPred values ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cardinality_of_filtered_subset_direct() {
    // Direct syntactic form: fast path through count_set_filter_elements.
    // Domain is SUBSET {1,2} (Value::Subset) — iter_set() works directly.
    assert_eq!(
        eval_str(r#"Cardinality({t \in SUBSET {1, 2} : 1 \in t})"#).unwrap(),
        Value::int(2) // {1} and {1,2}
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cardinality_of_let_bound_setpred() {
    // #1814: LET-bound SetPred goes through fallback path (not syntactic fast path).
    // The arg to Cardinality is Ref("S"), not SetFilter, so set_len() is called on
    // the SetPred value. Without the fix, this errors with "Cardinality not supported".
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
S == {t \in SUBSET {1, 2} : 1 \in t}
Op == Cardinality(S)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(
        result,
        Value::int(2),
        "Cardinality of SetPred via LET binding"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cardinality_of_nested_setpred_domain() {
    // #1814: Cardinality({x \in {y \in SUBSET S : P} : Q}) where domain is itself
    // a SetPred. count_set_filter_elements must handle SetPred domains.
    assert_eq!(
        eval_str(r#"Cardinality({x \in {y \in SUBSET {1, 2, 3} : 1 \in y} : 2 \in x})"#).unwrap(),
        Value::int(2) // {1,2} and {1,2,3}
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_count_set_filter_elements_not_cached_across_outer_quantifier() {
    // This exercises the direct Cardinality({y \in S : P}) fast path, which
    // uses count_set_filter_elements() instead of building the set. The filter
    // predicate depends on the outer x, so each iteration must re-evaluate it.
    assert_eq!(
        eval_str(
            r#"\A x \in {1, 2} :
                 Cardinality({y \in {1, 2, 3} : y > x}) = 3 - x"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

/// Regression test for #1830 audit: SetPred values tested against SUBSET membership.
/// eval_membership_lazy and set_contains_with_ctx must use eval_iter_set, not raw
/// iter_set(), so that SetPred elements are properly materialized for subset checks.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_in_subset_membership() {
    // A SetPred value (from {x \in S : P}) should be recognized as \in SUBSET S
    // because it is a valid set whose elements are all in S.
    // {x \in {1,2,3} : x > 1} produces {2,3}, and {2,3} \in SUBSET {1,2,3} is TRUE.
    assert_eq!(
        eval_str(r#"{x \in {1,2,3} : x > 1} \in SUBSET {1,2,3}"#).unwrap(),
        Value::Bool(true),
        "SetPred value should be member of SUBSET of its source"
    );
    // Also test the negative case: {2,3} \in SUBSET {1,2} is FALSE (3 not in {1,2}).
    assert_eq!(
        eval_str(r#"{x \in {1,2,3} : x > 1} \in SUBSET {1,2}"#).unwrap(),
        Value::Bool(false),
        "SetPred value should NOT be member of SUBSET when element not in base"
    );
}

/// Regression test for #1886/#1830: SUBSET membership must only coerce "not a set"
/// to FALSE; real SetPred evaluation failures must propagate as errors.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_in_subset_membership_propagates_predicate_error() {
    let err = eval_str(r#"{x \in {1,2} : 1} \in SUBSET {1,2}"#).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::TypeError {
                expected: "BOOLEAN",
                ..
            }
        ),
        "SetPred predicate type errors must propagate in SUBSET membership, got: {:?}",
        err
    );
}

// === #1814 regression tests: CHOOSE and function construction over SetPred ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_over_setpred_domain() {
    // #1814: CHOOSE x \in SetPred : P(x) where the domain is a LET-bound SetPred.
    // eval_choose calls iter_set_tlc_normalized → iter_set → as_lazy_set → None for SetPred.
    // Without eval_iter_set_tlc_normalized, this returns SetTooLarge.
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
S == {t \in SUBSET {1, 2} : 1 \in t}
Op == CHOOSE x \in S : 2 \in x
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    // The only subset of {1,2} containing both 1 and 2 is {1,2}
    assert_eq!(
        result,
        Value::set([Value::int(1), Value::int(2)]),
        "CHOOSE over SetPred domain should find {{1,2}}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_over_setpred_domain_direct_filter() {
    // Direct syntactic CHOOSE over filter expression (not LET-bound).
    // This may take a different path through eval_choose depending on whether
    // the parser recognizes the SetFilter pattern.
    assert_eq!(
        eval_str(r#"CHOOSE x \in {n \in 1..5 : n > 3} : x < 5"#).unwrap(),
        Value::int(4),
        "CHOOSE over direct set filter should find 4"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_function_construction_over_setpred_domain() {
    // Gap: function_values.rs:162 uses raw iter_set() which returns None for SetPred.
    // [x \in SetPred |-> expr] where SetPred is LET-bound should construct a function.
    // Without the fix, iter_set() returns None → the function domain is silently dropped.
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
S == {n \in 1..5 : n % 2 = 1}
Op == [x \in S |-> x * 10]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op");
    // S = {1, 3, 5}. The function [x \in S |-> x*10] should be <<10, 30, 50>> mapped by keys.
    // If this errors with a type error or produces wrong results, function_values.rs:162 gap.
    match result {
        Ok(val) => {
            // The function should map 1->10, 3->30, 5->50
            // Verify by applying the function
            let src2 = r#"
---- MODULE Test2 ----
EXTENDS FiniteSets
S == {n \in 1..5 : n % 2 = 1}
F == [x \in S |-> x * 10]
Op == F[3]
====
"#;
            let tree2 = parse_to_syntax_tree(src2);
            let lower_result2 = lower(FileId(0), &tree2);
            assert!(lower_result2.errors.is_empty());
            let module2 = lower_result2.module.unwrap();
            let mut ctx2 = EvalCtx::new();
            ctx2.load_module(&module2);
            let result2 = ctx2.eval_op("Op").unwrap();
            assert_eq!(
                result2,
                Value::int(30),
                "Function over SetPred domain: F[3] should be 30, got {:?}. \
                 This confirms function_values.rs handles SetPred domains.",
                val
            );
        }
        Err(e) => {
            panic!(
                "Function construction over SetPred domain failed: {:?}. \
                 This is the function_values.rs:162 gap — iter_set() returns None for SetPred.",
                e
            );
        }
    }
}

/// Part of #3907: Verify k-subset semantics for {x \in SUBSET S : Cardinality(x) = k}.
///
/// The k-subset optimization should produce correct results matching C(n,k)
/// combinatorial counts. This is critical for specs like SlushMedium where
/// direct C(n,k) generation replaces 2^n powerset enumeration.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_cardinality_eq_pattern() {
    // C(3,2) = 3 subsets of size 2 from {1,2,3}
    let val = eval_str(r#"Cardinality({x \in SUBSET {1, 2, 3} : Cardinality(x) = 2})"#).unwrap();
    assert_eq!(val, Value::int(3), "C(3,2) = 3");

    // Membership: {1,2} should be in the k=2 subsets
    let mem = eval_str(r#"{1, 2} \in {x \in SUBSET {1, 2, 3} : Cardinality(x) = 2}"#).unwrap();
    assert_eq!(mem, Value::Bool(true));

    // Non-membership: {1} is size 1, not size 2
    let non_mem = eval_str(r#"{1} \in {x \in SUBSET {1, 2, 3} : Cardinality(x) = 2}"#).unwrap();
    assert_eq!(non_mem, Value::Bool(false));
}

/// Part of #3907: k-subset edge cases — k=0, k=n, k>n
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_optimization_edge_cases() {
    clear_for_test_reset();
    // k=0: should yield {empty_set}
    let val_k0 = eval_str(r#"Cardinality({x \in SUBSET {1, 2} : Cardinality(x) = 0})"#).unwrap();
    assert_eq!(val_k0, Value::int(1), "C(2,0)=1: just the empty set");

    // k=n: should yield {full_set}
    let val_kn = eval_str(r#"Cardinality({x \in SUBSET {1, 2} : Cardinality(x) = 2})"#).unwrap();
    assert_eq!(val_kn, Value::int(1), "C(2,2)=1: just the full set");

    // k>n: should yield empty set
    let val_kbig =
        eval_str(r#"Cardinality({x \in SUBSET {1, 2} : Cardinality(x) = 5})"#).unwrap();
    assert_eq!(val_kbig, Value::int(0), "C(2,5)=0: impossible");
}

/// Regression test: function construction over SUBSET-backed SetPred domain.
/// `eval_func_def` must use EvalCtx-aware domain iteration for SetPred values.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_function_construction_over_subset_setpred_domain_bug() {
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
S == {s \in SUBSET {1, 2} : Cardinality(s) = 1}
F == [x \in S |-> Cardinality(x)]
Op == F[{1}]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    assert_eq!(
        ctx.eval_op("Op").unwrap(),
        Value::int(1),
        "F[{{1}}] should be Cardinality({{1}}) = 1"
    );
}
