// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Core tests for FlatZinc-to-SMT translation.
// Extended constraint coverage in tests_extended.rs.
// TranslateError tests in tests_error.rs.

use super::*;

fn translate_fzn(input: &str) -> TranslationResult {
    let model = z4_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

// --- Variable declaration tests ---

#[test]
fn test_declare_bool_var() {
    let r = translate_fzn("var bool: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Bool)"));
}

#[test]
fn test_declare_int_var() {
    let r = translate_fzn("var int: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Int)"));
}

#[test]
fn test_declare_int_range_var() {
    let r = translate_fzn("var 1..10: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Int)"));
    assert!(r.smtlib.contains("(assert (>= x 1))"));
    assert!(r.smtlib.contains("(assert (<= x 10))"));
}

#[test]
fn test_declare_int_set_var() {
    let r = translate_fzn("var {1, 3, 5}: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Int)"));
    assert!(r.smtlib.contains("(assert (or (= x 1) (= x 3) (= x 5)))"));
}

#[test]
fn test_declare_array_var() {
    let r = translate_fzn("array [1..3] of var 1..5: q;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const q_1 Int)"));
    assert!(r.smtlib.contains("(declare-const q_2 Int)"));
    assert!(r.smtlib.contains("(declare-const q_3 Int)"));
    assert!(r.smtlib.contains("(assert (>= q_1 1))"));
    assert!(r.smtlib.contains("(assert (<= q_1 5))"));
}

#[test]
fn test_var_with_fixed_value() {
    let r = translate_fzn("var bool: x = true;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(assert (= x true))"));
}

// Regression test for z4#5355: interleaved declare/assert causes z4 hang.
// All (declare-const) must come before all (assert) bound statements.
#[test]
fn test_deferred_bounds_ordering() {
    let r = translate_fzn(
        "var 1..10: x;\nvar 1..10: y;\nvar 1..10: z;\n\
         constraint int_ne(x, y);\nsolve satisfy;\n",
    );
    let lines: Vec<&str> = r.smtlib.lines().collect();
    let last_declare = lines
        .iter()
        .rposition(|l| l.starts_with("(declare-const"))
        .expect("no declare-const found");
    let first_assert = lines
        .iter()
        .position(|l| l.starts_with("(assert"))
        .expect("no assert found");
    assert!(
        last_declare < first_assert,
        "declare-const at line {last_declare} comes after assert at line {first_assert}\n\
         Output:\n{}",
        r.smtlib
    );
}

// Stress test: many variables to verify deferred-bounds holds at scale.
// For n variables, all n declare-const lines must precede all n bound assertions.
#[test]
fn test_deferred_bounds_ordering_many_vars() {
    let mut fzn = String::new();
    for i in 0..20 {
        fzn.push_str(&format!("var 1..100: v{i};\n"));
    }
    // Add constraints that reference multiple variables
    fzn.push_str("constraint int_ne(v0, v1);\n");
    fzn.push_str("constraint int_le(v2, v3);\n");
    fzn.push_str("solve satisfy;\n");

    let r = translate_fzn(&fzn);
    let lines: Vec<&str> = r.smtlib.lines().collect();
    let last_declare = lines
        .iter()
        .rposition(|l| l.starts_with("(declare-const"))
        .expect("no declare-const found");
    let first_assert = lines
        .iter()
        .position(|l| l.starts_with("(assert"))
        .expect("no assert found");
    assert!(
        last_declare < first_assert,
        "With 20 variables: declare-const at line {} comes after assert at line {}\n\
         First 30 lines:\n{}",
        last_declare,
        first_assert,
        lines
            .iter()
            .take(30)
            .copied()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// Verify alldifferent pairwise encoding produces exactly n*(n-1)/2 assertions.
// Documents the O(n^2) encoding cost from globals.rs.
#[test]
fn test_alldifferent_pairwise_count() {
    let r = translate_fzn(
        "array [1..5] of var 1..5: x;\n\
         constraint fzn_all_different_int(x);\nsolve satisfy;\n",
    );
    let neq_count = r
        .smtlib
        .lines()
        .filter(|l| l.contains("(assert (not (= x_"))
        .count();
    // 5 variables -> 5*4/2 = 10 pairwise assertions
    assert_eq!(
        neq_count, 10,
        "Expected 10 pairwise != assertions for 5 variables, got {neq_count}"
    );
}

#[test]
fn test_parameter_inlining() {
    let r = translate_fzn("int: n = 42;\nvar int: x;\nconstraint int_eq(x, n);\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(assert (= x 42))"));
}

// --- Basic constraint tests ---

#[test]
fn test_int_eq() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_eq(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x y))"));
}

#[test]
fn test_int_ne() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_ne(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= x y)))"));
}

#[test]
fn test_int_lt() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lt(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (< x y))"));
}

#[test]
fn test_int_le() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_le(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= x y))"));
}

// --- Boolean constraint tests ---

#[test]
fn test_bool_and() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_and(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (and a b)))"));
    assert!(r.smtlib.contains("(assert (=> (and a b) r))"));
}

#[test]
fn test_bool_or() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_or(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (or a b)))"));
    assert!(r.smtlib.contains("(assert (=> (or a b) r))"));
}

#[test]
fn test_bool_not() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint bool_not(a, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (not a)))"));
    assert!(r.smtlib.contains("(assert (=> (not a) b))"));
}

#[test]
fn test_bool_clause() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\n\
         constraint bool_clause([a, b], [c]);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or a b (not c)))"));
}

// --- Arithmetic constraint tests ---

#[test]
fn test_int_plus() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_plus(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (+ x y)))"));
}

#[test]
fn test_int_times() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (* x y)))"));
}

#[test]
fn test_int_abs() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_abs(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= y (ite (>= x 0) x (- x))))"));
}

#[test]
fn test_int_min() {
    let r = translate_fzn(
        "var int: a;\nvar int: b;\nvar int: c;\n\
         constraint int_min(a, b, c);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= c (ite (<= a b) a b)))"));
}

#[test]
fn test_int_max() {
    let r = translate_fzn(
        "var int: a;\nvar int: b;\nvar int: c;\n\
         constraint int_max(a, b, c);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= c (ite (>= a b) a b)))"));
}

// --- Linear constraint tests ---

#[test]
fn test_int_lin_eq() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_eq([1, -1], [x, y], 0);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= (+ x (- y)) 0))"));
}

#[test]
fn test_int_lin_le() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_le([2, 3], [x, y], 10);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= (+ (* 2 x) (* 3 y)) 10))"));
}

#[test]
fn test_int_lin_ne() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_ne([1, 1], [x, y], 5);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= (+ x y) 5)))"));
}

#[test]
fn test_int_lin_with_param_coefficients() {
    let r = translate_fzn(
        "array [1..2] of int: cs = [3, 4];\n\
         var int: x;\nvar int: y;\n\
         constraint int_lin_eq(cs, [x, y], 12);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= (+ (* 3 x) (* 4 y)) 12))"));
}

// --- Array element tests ---

#[test]
fn test_array_int_element() {
    let r = translate_fzn(
        "var 1..3: idx;\narray [1..3] of var 1..5: arr;\nvar 1..5: val;\n\
         constraint array_int_element(idx, arr, val);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= val (ite (= idx 1) arr_1"));
}

// --- Type conversion tests ---

#[test]
fn test_bool2int() {
    let r = translate_fzn(
        "var bool: b;\nvar int: i;\n\
         constraint bool2int(b, i);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= i (ite b 1 0)))"));
}

// --- Set membership tests ---

#[test]
fn test_set_in_literal() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, {1, 3, 5});\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or (= x 1) (= x 3) (= x 5)))"));
}

#[test]
fn test_set_in_range() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, 1..5);\nsolve satisfy;\n",
    );
    // Range expands to individual equalities
    assert!(r.smtlib.contains("(assert (or (= x 1) (= x 2)"));
}

// --- Global constraint tests ---

#[test]
fn test_alldifferent() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: x;\n\
         constraint fzn_all_different_int(x);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= x_1 x_2)))"));
    assert!(r.smtlib.contains("(assert (not (= x_1 x_3)))"));
    assert!(r.smtlib.contains("(assert (not (= x_2 x_3)))"));
}

// --- Objective tests ---

#[test]
fn test_solve_satisfy() {
    let r = translate_fzn("var int: x;\nsolve satisfy;\n");
    assert!(r.objective.is_none());
    assert!(r.smtlib.contains("(check-sat)"));
}

#[test]
fn test_solve_minimize() {
    let r = translate_fzn("var int: obj;\nsolve minimize obj;\n");
    let obj = r.objective.as_ref().expect("should have objective");
    assert!(obj.minimize);
    assert_eq!(obj.smt_expr, "obj");
}

#[test]
fn test_solve_maximize() {
    let r = translate_fzn("var int: obj;\nsolve maximize obj;\n");
    let obj = r.objective.as_ref().expect("should have objective");
    assert!(!obj.minimize);
    assert_eq!(obj.smt_expr, "obj");
}

// --- Output variable tests ---

#[test]
fn test_output_var_annotation() {
    let r = translate_fzn("var 1..5: x :: output_var;\nsolve satisfy;\n");
    assert_eq!(r.output_vars.len(), 1);
    assert_eq!(r.output_vars[0].fzn_name, "x");
    assert!(!r.output_vars[0].is_array);
}

#[test]
fn test_output_array_annotation() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: q :: output_array([1..3]);\n\
         solve satisfy;\n",
    );
    assert_eq!(r.output_vars.len(), 1);
    assert_eq!(r.output_vars[0].fzn_name, "q");
    assert!(r.output_vars[0].is_array);
    assert_eq!(r.output_vars[0].array_range, Some((1, 3)));
    assert_eq!(r.output_vars[0].smt_names.len(), 3);
}

// --- Integration: N-Queens model ---

#[test]
fn test_nqueens_4_model() {
    let input = "\
        int: n = 4;\n\
        array [1..4] of var 1..4: q :: output_array([1..4]);\n\
        constraint fzn_all_different_int(q);\n\
        constraint int_ne(q[1], q[2]);\n\
        solve satisfy;\n";
    let r = translate_fzn(input);
    // Should have 4 array elements declared
    assert!(r.smtlib.contains("(declare-const q_1 Int)"));
    assert!(r.smtlib.contains("(declare-const q_4 Int)"));
    // Bounds for each element
    assert!(r.smtlib.contains("(assert (>= q_1 1))"));
    assert!(r.smtlib.contains("(assert (<= q_1 4))"));
    // Alldifferent pairwise
    assert!(r.smtlib.contains("(assert (not (= q_1 q_2)))"));
    assert!(r.smtlib.contains("(assert (not (= q_3 q_4)))"));
    // Direct constraint using array access
    assert!(r.smtlib.contains("(assert (not (= q_1 q_2)))"));
    // Output variable tracking
    assert_eq!(r.output_vars.len(), 1);
    assert_eq!(r.output_vars[0].fzn_name, "q");
    assert_eq!(r.output_vars[0].smt_names.len(), 4);
    // check-sat and get-value present
    assert!(r.smtlib.contains("(check-sat)"));
    assert!(r.smtlib.contains("(get-value ("));
}

// --- int_times linearization tests ---

#[test]
fn test_int_times_linearized_small_domain() {
    // When one operand has a small range (0..3 = 4 values), int_times should
    // linearize via ITE chain instead of using nonlinear `*`.
    let r = translate_fzn(
        "var 0..3: a;\nvar int: b;\nvar int: r;\n\
         constraint int_times(a, b, r);\nsolve satisfy;\n",
    );
    // Should NOT contain bare multiplication
    assert!(
        !r.smtlib.contains("(assert (= r (* a b)))"),
        "Expected linearized ITE, not bare multiplication:\n{}",
        r.smtlib
    );
    // Should contain ITE chain with domain values 0, 1, 2, 3
    assert!(
        r.smtlib.contains("(ite (= a 0)"),
        "Expected ITE for a=0:\n{}",
        r.smtlib
    );
    assert!(
        r.smtlib.contains("(ite (= a 1)"),
        "Expected ITE for a=1:\n{}",
        r.smtlib
    );
    // Value 0 should produce "0" (not (* 0 b))
    assert!(
        r.smtlib.contains("(ite (= a 0) 0"),
        "Expected 0 for a*b when a=0:\n{}",
        r.smtlib
    );
    // Value 1 should produce "b" (not (* 1 b))
    assert!(
        r.smtlib.contains("(ite (= a 1) b"),
        "Expected b for a*b when a=1:\n{}",
        r.smtlib
    );
    // Logic should be QF_LIA, not QF_NIA
    assert!(
        r.smtlib.contains("(set-logic QF_LIA)"),
        "Expected QF_LIA after linearization, got:\n{}",
        r.smtlib.lines().next().unwrap_or("")
    );
}

#[test]
fn test_int_times_linearized_second_operand() {
    // When the second operand is small-domain, should also linearize.
    let r = translate_fzn(
        "var int: a;\nvar 0..2: b;\nvar int: r;\n\
         constraint int_times(a, b, r);\nsolve satisfy;\n",
    );
    assert!(
        !r.smtlib.contains("(assert (= r (* a b)))"),
        "Expected linearized ITE, not bare multiplication:\n{}",
        r.smtlib
    );
    assert!(
        r.smtlib.contains("(ite (= b"),
        "Expected ITE on b (second operand):\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_times_unbounded_stays_nonlinear() {
    // When both operands are unbounded, should use nonlinear `*`.
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(assert (= z (* x y)))"),
        "Expected nonlinear multiplication for unbounded vars:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_times_bool_operand_linearized() {
    // Bool variables have domain {0, 1} and should trigger linearization.
    let r = translate_fzn(
        "var bool: flag;\nvar int: x;\nvar int: r;\n\
         var 0..1: flag_int;\n\
         constraint bool2int(flag, flag_int);\n\
         constraint int_times(flag_int, x, r);\nsolve satisfy;\n",
    );
    // 0..1 domain should linearize: ite(flag_int=0, 0, x)
    assert!(
        !r.smtlib.contains("(* flag_int x)"),
        "Expected linearized ITE for 0..1 domain:\n{}",
        r.smtlib
    );
}

// --- Error handling tests ---

#[test]
fn test_unsupported_constraint_error() {
    let input = "var int: x;\nconstraint unknown_constraint(x);\nsolve satisfy;\n";
    let model = z4_flatzinc_parser::parse_flatzinc(input).unwrap();
    let err = translate(&model).unwrap_err();
    assert!(
        matches!(err, TranslateError::UnsupportedConstraint(ref s) if s == "unknown_constraint")
    );
}

// --- Edge case tests ---

#[test]
fn test_empty_model() {
    let r = translate_fzn("solve satisfy;\n");
    assert!(r.smtlib.contains("(check-sat)"));
    assert!(r.output_vars.is_empty());
    assert!(r.objective.is_none());
}

#[test]
fn test_single_element_set_in() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, {42});\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x 42))"));
}

#[test]
fn test_negative_int_in_smt() {
    let r = translate_fzn(
        "int: n = -5;\nvar int: x;\n\
         constraint int_eq(x, n);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x (- 5)))"));
}
