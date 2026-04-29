// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for FiniteSets and FiniteSetsExt operators in `builtin_finite_sets`.

use super::{eval_str, eval_with_ops};
use crate::error::EvalError;
use crate::Value;

#[test]
fn test_is_finite_set_true() {
    let v = eval_str("IsFiniteSet({1, 2, 3})").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_finite_set_empty() {
    let v = eval_str("IsFiniteSet({})").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_finite_set_non_set() {
    let v = eval_str("IsFiniteSet(42)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// === #1508 regression tests: IsFiniteSet must return FALSE for infinite sets ===

#[test]
fn test_is_finite_set_nat_infinite() {
    // Nat is infinite — IsFiniteSet(Nat) must be FALSE (TLC parity)
    let v = eval_with_ops("EXTENDS FiniteSets, Naturals", "IsFiniteSet(Nat)").unwrap();
    assert_eq!(
        v,
        Value::Bool(false),
        "#1508: IsFiniteSet(Nat) must be FALSE"
    );
}

#[test]
fn test_is_finite_set_int_infinite() {
    // Int is infinite — IsFiniteSet(Int) must be FALSE
    let v = eval_with_ops("EXTENDS FiniteSets, Integers", "IsFiniteSet(Int)").unwrap();
    assert_eq!(
        v,
        Value::Bool(false),
        "#1508: IsFiniteSet(Int) must be FALSE"
    );
}

#[test]
fn test_is_finite_set_real_infinite() {
    // Real is infinite — IsFiniteSet(Real) must be FALSE
    let v = eval_with_ops("EXTENDS FiniteSets, Reals", "IsFiniteSet(Real)").unwrap();
    assert_eq!(
        v,
        Value::Bool(false),
        "#1508: IsFiniteSet(Real) must be FALSE"
    );
}

#[test]
fn test_is_finite_set_string_infinite() {
    // STRING is infinite — IsFiniteSet(STRING) must be FALSE
    let v = eval_with_ops("EXTENDS FiniteSets, TLC", "IsFiniteSet(STRING)").unwrap();
    assert_eq!(
        v,
        Value::Bool(false),
        "#1508: IsFiniteSet(STRING) must be FALSE"
    );
}

#[test]
fn test_is_finite_set_interval_finite() {
    // 1..10 is finite — IsFiniteSet(1..10) must be TRUE
    let v = eval_with_ops("EXTENDS FiniteSets, Naturals", "IsFiniteSet(1..10)").unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#1508: IsFiniteSet(1..10) must be TRUE"
    );
}

#[test]
fn test_sym_diff_disjoint() {
    // SymDiff of disjoint sets is their union
    let v = eval_str("SymDiff({1, 2}, {3, 4}) = {1, 2, 3, 4}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_sym_diff_overlapping() {
    // SymDiff removes common elements
    let v = eval_str("SymDiff({1, 2, 3}, {2, 3, 4}) = {1, 4}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_sym_diff_identical() {
    // SymDiff of identical sets is empty
    let v = eval_str("SymDiff({1, 2}, {1, 2}) = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_flatten_set_of_sets() {
    let v = eval_str("Flatten({{1, 2}, {2, 3}, {3, 4}}) = {1, 2, 3, 4}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_flatten_empty() {
    let v = eval_str("Flatten({}) = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_choose_from_set() {
    // Choose(S) returns first element in sorted order
    let v = eval_str("Choose({3, 1, 2})").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_choose_empty_set_errors() {
    let err = eval_str("Choose({})").unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("non-empty")
            || msg.contains("Choose")
            || matches!(err, EvalError::ChooseFailed { .. }),
        "Expected Choose-related error, got: {}",
        msg
    );
}

#[test]
fn test_sum_set_of_integers() {
    let v = eval_str("Sum({1, 2, 3, 4, 5})").unwrap();
    assert_eq!(v, Value::SmallInt(15));
}

#[test]
fn test_sum_empty_set() {
    let v = eval_str("Sum({})").unwrap();
    assert_eq!(v, Value::SmallInt(0));
}

#[test]
fn test_sum_negative_integers() {
    let v = eval_str("Sum({-3, -2, -1, 0, 1, 2, 3})").unwrap();
    assert_eq!(v, Value::SmallInt(0));
}

#[test]
fn test_product_set_of_integers() {
    let v = eval_str("Product({1, 2, 3, 4})").unwrap();
    assert_eq!(v, Value::SmallInt(24));
}

#[test]
fn test_product_empty_set() {
    // Product of empty set is 1 (multiplicative identity)
    let v = eval_str("Product({})").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_product_with_zero() {
    let v = eval_str("Product({0, 1, 2, 3})").unwrap();
    assert_eq!(v, Value::SmallInt(0));
}

#[test]
fn test_mean_set_of_integers() {
    // Mean({1,2,3,4,5}) = 15/5 = 3
    let v = eval_str("Mean({1, 2, 3, 4, 5})").unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

#[test]
fn test_mean_integer_division() {
    // Mean({1,2}) = 3/2 = 1 (floor division)
    let v = eval_str("Mean({1, 2})").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_mean_empty_set_errors() {
    let err = eval_str("Mean({})").unwrap_err();
    assert!(
        matches!(err, EvalError::Internal { ref message, .. } if message.contains("non-empty")),
        "Expected Internal error about non-empty set, got: {:?}",
        err
    );
}

#[test]
fn test_ksubsets_cardinality() {
    // Ksubsets({1,2,3}, 2) = {{1,2}, {1,3}, {2,3}} — verify exact contents
    let v = eval_str("Ksubsets({1, 2, 3}, 2) = {{1, 2}, {1, 3}, {2, 3}}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_ksubsets_zero() {
    // Ksubsets(S, 0) = {{}} — one subset (empty set)
    let v = eval_str("Cardinality(Ksubsets({1, 2, 3}, 0))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_ksubsets_full() {
    // Ksubsets(S, |S|) = {S} — one subset (the full set)
    let v = eval_str("Cardinality(Ksubsets({1, 2, 3}, 3))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_quantify_with_predicate() {
    // Quantify(S, P) counts elements satisfying P
    let v = eval_with_ops(
        "IsEven(x) == x % 2 = 0",
        "Quantify({1, 2, 3, 4, 5, 6}, IsEven)",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

#[test]
fn test_quantify_none_satisfy() {
    let v = eval_with_ops("IsNeg(x) == x < 0", "Quantify({1, 2, 3}, IsNeg)").unwrap();
    assert_eq!(v, Value::SmallInt(0));
}

#[test]
fn test_reduce_set_sum() {
    // ReduceSet(Op, S, base) — fold over set
    let v = eval_with_ops("Add(a, b) == a + b", "ReduceSet(Add, {1, 2, 3, 4}, 0)").unwrap();
    assert_eq!(v, Value::SmallInt(10));
}

#[test]
fn test_map_then_sum_set() {
    // MapThenSumSet(Op, S) — map then sum
    let v = eval_with_ops("Double(x) == x * 2", "MapThenSumSet(Double, {1, 2, 3})").unwrap();
    assert_eq!(v, Value::SmallInt(12));
}

#[test]
fn test_choices_two_sets() {
    // Choices({{1,2}, {3,4}}) = all choice functions
    // 2 choices per set × 2 sets = 4 functions
    let v = eval_str("Cardinality(Choices({{1, 2}, {3, 4}}))").unwrap();
    assert_eq!(v, Value::SmallInt(4));
}

#[test]
fn test_choices_empty_inner_set() {
    // If any set is empty, no choice functions exist
    let v = eval_str("Choices({{1, 2}, {}}) = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_choices_empty_outer_set() {
    // Empty set of sets → one choice function (the empty function)
    let v = eval_str("Cardinality(Choices({}))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_choose_unique_found() {
    // ChooseUnique({1,2,3}, LAMBDA x: x = 2) = 2
    let v = eval_str("ChooseUnique({1, 2, 3}, LAMBDA x: x = 2)").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_choose_unique_multiple_errors() {
    // Multiple elements satisfy the predicate
    let err = eval_str("ChooseUnique({1, 2, 3}, LAMBDA x: x > 1)").unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("more than one"),
        "Expected 'more than one element' error, got: {}",
        msg
    );
}

#[test]
fn test_choose_unique_none_errors() {
    // No element satisfies the predicate
    let err = eval_str("ChooseUnique({1, 2, 3}, LAMBDA x: x > 10)").unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("no element"),
        "Expected 'no element satisfies' error, got: {}",
        msg
    );
}

// === #1899 regression tests: FiniteSetsExt operators with SetPred inputs ===
// SetPred values arise from {x \in SUBSET S : P(x)} via the #1455 lazy optimization.
// Before #1899, all FiniteSetsExt operators called as_set() which returns None for SetPred.

#[test]
fn test_flatten_setpred_input() {
    // Flatten(SetPred) where SetPred = {{1}, {1,2}} → UNION = {1, 2}
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "Flatten(S) = {1, 2}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true), "#1899: Flatten must accept SetPred");
}

#[test]
fn test_choose_setpred_input() {
    // Choose(SetPred) where SetPred = {{1}, {1,2}} → {1} (first in sorted order)
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "Choose(S) = {1}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true), "#1899: Choose must accept SetPred");
}

#[test]
fn test_sym_diff_setpred_input() {
    // SymDiff(SetPred, concrete) where SetPred = {{1}, {1,2}}
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "SymDiff(S, {{1}}) = {{1, 2}}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true), "#1899: SymDiff must accept SetPred");
}

#[test]
fn test_choose_unique_setpred_input() {
    // ChooseUnique(SetPred, pred) where SetPred = {{1}, {1,2}}
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "ChooseUnique(S, LAMBDA s: Cardinality(s) = 2) = {1, 2}",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#1899: ChooseUnique must accept SetPred"
    );
}

#[test]
fn test_quantify_setpred_input() {
    // Quantify(SetPred, pred) where SetPred = {{}, {1}, {2}, {1,2}}
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nIsNonEmpty(s) == s /= {}\nS == {x \\in SUBSET {1, 2} : TRUE}",
        "Quantify(S, IsNonEmpty)",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(3), "#1899: Quantify must accept SetPred");
}

#[test]
fn test_reduce_set_setpred_input() {
    // ReduceSet(Op, SetPred, base) — fold over SetPred elements
    // SetPred = {{1}, {1,2}} — union-fold: {} ∪ {1} ∪ {1,2} = {1, 2}
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nUnionOp(acc, s) == acc \\cup s\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "ReduceSet(UnionOp, S, {}) = {1, 2}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true), "#1899: ReduceSet must accept SetPred");
}

#[test]
fn test_map_then_sum_setpred_input() {
    // MapThenSumSet(Cardinality, SetPred) where SetPred = {{1}, {1,2}}
    // Cardinality({1}) + Cardinality({1,2}) = 1 + 2 = 3
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nCard(s) == Cardinality(s)\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "MapThenSumSet(Card, S)",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::SmallInt(3),
        "#1899: MapThenSumSet must accept SetPred"
    );
}

#[test]
fn test_choices_setpred_input() {
    // Choices(SetPred) where SetPred = {{1}, {1,2}} → choice functions
    // Each function picks one from {1} (only 1) and one from {1,2} (1 or 2) → 2 functions
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "Cardinality(Choices(S))",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(2), "#1899: Choices must accept SetPred");
}

// === FoldSet with SetPred input ===
// Issue #1894: Zero-arg operators returning SetPred are now eagerly materialized
// to concrete sets in eval_ident_shared_zero_arg_op. This means FoldSet receives
// a concrete Value::Set instead of Value::SetPred, so as_set() succeeds.

#[test]
fn test_foldset_setpred_input_via_zero_arg_op() {
    // FoldSet(Op, base, S) where S is a zero-arg operator returning SetPred.
    // S == {x \in SUBSET {1, 2} : 1 \in x} = {{1}, {1,2}}
    // FoldSet(LAMBDA a, s: a \cup s, {}, S) should produce {1, 2}
    let result = eval_with_ops(
        "EXTENDS FiniteSets\nUnionOp(a, s) == a \\cup s\nS == {x \\in SUBSET {1, 2} : 1 \\in x}",
        "FoldSet(UnionOp, {}, S) = {1, 2}",
    );
    assert_eq!(
        result.unwrap(),
        Value::Bool(true),
        "FoldSet over zero-arg operator returning SetPred should succeed \
         after #1894 materialization fix",
    );
}

// === Regression tests for #2269: named set operators with SetPred operands ===

#[test]
fn test_reduce_set_union_with_setpred_accumulator() {
    // Regression for #2269: ReduceSet where accumulator \cup element involves
    // a SetPred intermediate. The union operator must use lazy SetCup fallback
    // when to_sorted_set() returns None for SetPred.
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\n\
         S == {x \\in 1..5 : x > 2}\n\
         UnionAll(acc, s) == acc \\cup s",
        "ReduceSet(UnionAll, {{1, 2}, {4, 5}}, S) = {1, 2, 3, 4, 5}",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#2269: ReduceSet union fold with SetPred base must produce correct result"
    );
}

#[test]
fn test_reduce_set_intersection_with_setpred_accumulator() {
    // Regression for #2269: ReduceSet where accumulator \cap element involves SetPred.
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\n\
         S == {x \\in 1..5 : x > 2}\n\
         IntersectAll(acc, s) == acc \\cap s",
        "ReduceSet(IntersectAll, {{3, 4, 5, 6}}, S) = {3, 4, 5}",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#2269: ReduceSet intersection fold with SetPred base must produce correct result"
    );
}

#[test]
fn test_reduce_set_difference_with_setpred_accumulator() {
    // Regression for #2269: ReduceSet where accumulator \ element involves SetPred.
    let v = eval_with_ops(
        "EXTENDS FiniteSets, FiniteSetsExt\n\
         S == {x \\in 1..10 : x > 5}\n\
         DiffAll(acc, s) == acc \\ {s}",
        "ReduceSet(DiffAll, {6, 7}, S) = {8, 9, 10}",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#2269: ReduceSet difference fold with SetPred base must produce correct result"
    );
}

#[test]
fn test_reduce_set_builtin_opref_cap() {
    // Part of #3075: ReduceSet with built-in operator reference (\cap).
    // Exercises the Expr::OpRef path in the ReduceSet builtin handler.
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "ReduceSet(\\cap, {{1, 2, 3}, {2, 3, 4}}, {1, 2, 3, 4}) = {2, 3}",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#3075: ReduceSet with \\cap OpRef must produce correct intersection"
    );
}

#[test]
fn test_reduce_set_builtin_opref_cup() {
    // Part of #3075: ReduceSet with built-in operator reference (\cup).
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "ReduceSet(\\cup, {{1, 2}, {3, 4}}, {}) = {1, 2, 3, 4}",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#3075: ReduceSet with \\cup OpRef must produce correct union"
    );
}

#[test]
fn test_reduce_set_builtin_opref_plus() {
    // Part of #3075: ReduceSet with built-in operator reference (+).
    let v = eval_with_ops("EXTENDS FiniteSets", "ReduceSet(+, {1, 2, 3, 4}, 0)").unwrap();
    assert_eq!(
        v,
        Value::SmallInt(10),
        "#3075: ReduceSet with + OpRef must produce correct sum"
    );
}

#[test]
fn test_reduce_set_user_defined_shadow_overridden() {
    // Part of #3075: User-defined ReduceSet (MCKVsnap Util.tla pattern) is overridden
    // by the builtin. The user-defined version uses SUBSET recursion (O(2^n)) but the
    // builtin does O(n) iteration. Result must be identical.
    let v = eval_with_ops(
        "EXTENDS FiniteSets\n\
         RECURSIVE ReduceSetSlow(_, _, _)\n\
         ReduceSetSlow(op(_, _), set, base) ==\n\
           IF set = {} THEN base\n\
           ELSE LET x == CHOOSE x \\in set: TRUE\n\
                IN  op(x, ReduceSetSlow(op, set \\ {x}, base))\n\
         Add(a, b) == a + b",
        "ReduceSet(Add, {1, 2, 3, 4}, 0) = ReduceSetSlow(Add, {1, 2, 3, 4}, 0)",
    )
    .unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "#3075: builtin ReduceSet override must produce same result as recursive version"
    );
}
