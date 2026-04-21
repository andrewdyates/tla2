// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_cegqi_valid_implication() {
    // forall x. (x > 0) => (x >= 1) is valid for integers
    // CE lemma: Not((e > 0) => (e >= 1)) = (e > 0) AND Not(e >= 1) = (e > 0) AND (e < 1)
    // For integers: e > 0 AND e < 1 is UNSAT (no integers in (0,1))
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (=> (> x 0) (>= x 1))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid quantified formula - CEGQI proves it via CE lemma being UNSAT
    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_cegqi_invalid_strict_positive() {
    // forall x. x > 0 is NOT valid (counterexample: x = 0 or x = -1)
    // #3441: Enumerative instantiation finds ground term 0, adds (0 > 0) = false.
    // This directly refutes the forall, proving UNSAT.
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (> x 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Invalid forall: enumerative instantiation with x=0 produces false,
    // proving the formula unsatisfiable.
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_cegqi_valid_nonstrict_positive() {
    // forall x. (x >= 0) => (x + 1 > 0) is valid
    // CE lemma: Not((e >= 0) => (e + 1 > 0)) = (e >= 0) AND (e + 1 <= 0)
    // This means e >= 0 AND e <= -1, which is UNSAT
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (=> (>= x 0) (> (+ x 1) 0))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid quantified formula
    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_cegqi_exists_witness_sat() {
    // exists x. x > 0 is satisfiable (witness: x = 1).
    // CE lemma for exists is phi(e) (no negation), which is SAT.
    let input = r#"
        (set-logic QF_LIA)
        (assert (exists ((x Int)) (> x 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
/// #7883: triggerless quantifiers over Seq-sorted binders must not enter
/// arithmetic CEGQI.
///
/// This sunder-style standard-library axiom mixes a non-arithmetic binder
/// sort (`Seq`) with an Int-valued accessor. The formula is satisfiable: the
/// model can interpret `seq_len` as a non-negative function, and the concrete
/// ground term `a` is consistent with `seq_len(a) = 0`.
///
/// The arithmetic sort guard should leave this quantifier to the general
/// triggerless path instead of creating a CE lemma over a Seq binder.
#[test]
fn test_cegqi_seq_binder_guard_end_to_end_7883() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_len (Seq) Int)
        (declare-const a Seq)
        (assert (= (seq_len a) 0))
        (assert (forall ((s Seq)) (>= (seq_len s) 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["sat"],
        "non-arithmetic Seq binders must not cause false-UNSAT via arithmetic CEGQI"
    );
}
/// Test that arithmetic CEGQI with bound-based instantiation works (#5690).
///
/// This test exercises the ArithInstantiator in the CEGQI refinement loop:
/// 1. CEGQI creates CE lemma for the forall (negation of body)
/// 2. CE lemma is SAT (counterexample found) or the CE lemma + bounds
///    directly determine the formula status
/// 3. ArithInstantiator collects bounds and computes selection terms
///
/// Formula: forall x. (x >= 0 AND x <= 5) => (2*x <= 10)
/// This is VALID: if 0 <= x <= 5, then 2x <= 10.
/// CE lemma: NOT((e >= 0 AND e <= 5) => (2*e <= 10))
///         = (e >= 0) AND (e <= 5) AND NOT(2*e <= 10)
///         = (e >= 0) AND (e <= 5) AND (2*e > 10)
/// For integers: 0 <= e <= 5 AND 2e > 10, so e > 5 AND e <= 5 → UNSAT.
/// CEGQI proves this directly via CE lemma.
#[test]
fn test_cegqi_arith_bounds_valid_implication_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (and (>= x 0) (<= x 5))
                (<= (* 2 x) 10))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid quantified formula — CEGQI proves via CE lemma UNSAT
    assert_eq!(outputs, vec!["sat"]);
}
/// Test arithmetic CEGQI refinement with model-based instantiation (#5690).
///
/// This exercises the case where CEGQI's CE lemma returns SAT (counterexample
/// found), triggering the ArithInstantiator-based refinement in
/// try_cegqi_arith_refinement. The refinement extracts model values for CE
/// variables, computes selection terms using bound analysis, and adds a ground
/// instantiation that proves the formula unsatisfiable.
///
/// Formula: forall x. NOT(x + 1 > x)
/// This is INVALID (x + 1 > x is always true).
/// The assertion says the universally quantified NOT(x+1 > x) holds,
/// which is equivalent to asserting "false for all x" — UNSAT.
///
/// CE lemma: NOT(NOT(e + 1 > e)) = (e + 1 > e)
/// This is SAT (any integer e works), so refinement fires.
/// Refinement creates phi(model_value) = NOT(v + 1 > v) = false for any v.
/// Adding this ground instance makes the system UNSAT.
#[test]
fn test_cegqi_arith_refinement_invalid_formula_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (not (> (+ x 1) x))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Invalid formula — should be UNSAT (the forall of a falsehood can't hold).
    // Before #5690: could return "unknown" if enumerative didn't fire.
    // After #5690: CEGQI refinement instantiates with model value, proves UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}
/// Test CEGQI with strict inequality bounds (#5690, P1:16 strictness audit).
///
/// This exercises ArithInstantiator's handling of strict `<` and `>` operators.
/// The formula uses `<` (strict less-than) rather than `<=` (weak):
///   forall x. (x > 0 AND x < 5) => (x >= 1 AND x <= 4)
///
/// This is VALID for integers: if 0 < x < 5, then 1 <= x <= 4.
/// CE lemma: (e > 0) AND (e < 5) AND NOT(e >= 1 AND e <= 4)
///         = (e > 0) AND (e < 5) AND (e < 1 OR e > 4)
/// For integers: 1 <= e <= 4 AND (e < 1 OR e > 4) → UNSAT.
///
/// If ArithInstantiator treats `<` the same as `<=` (no strictness tracking),
/// it might select boundary values 0 or 5 which violate the strict bounds.
/// For integer arithmetic this is less critical (x < 5 ↔ x <= 4), but the
/// bound collection must still handle strict operators correctly.
#[test]
fn test_cegqi_arith_strict_bounds_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (and (> x 0) (< x 5))
                (and (>= x 1) (<= x 4)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid formula — should be SAT (the universal quantification holds).
    assert_eq!(outputs, vec!["sat"]);
}
/// Test CEGQI with NOT(strict) bounds — exercises Not(<) and Not(>) paths.
///
/// Formula: forall x. NOT(x < 3) => (x >= 3)
/// This is VALID: NOT(x < 3) is x >= 3.
/// CE lemma: NOT(NOT(e < 3) => (e >= 3)) = NOT(e < 3) AND NOT(e >= 3)
///         = (e >= 3) AND (e < 3) → UNSAT for integers.
///
/// If ArithInstantiator doesn't handle Not(<), the bound from NOT(e < 3)
/// (which is e >= 3) will be silently dropped, potentially causing the
/// refinement loop to fail or select a wrong instantiation.
#[test]
fn test_cegqi_arith_negated_strict_bounds_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (not (< x 3))
                (>= x 3))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid formula — should be SAT.
    assert_eq!(outputs, vec!["sat"]);
}
/// Test CEGQI refinement with strict bound at the boundary (#5690, P1:16).
///
/// This INVALID formula requires CEGQI refinement (CE lemma is SAT) and
/// tests whether the ArithInstantiator correctly handles strict vs weak
/// bounds at the exact boundary value.
///
/// Formula: forall x. (x > 0) => (x > 1)
/// INVALID: x=1 satisfies x>0 but not x>1.
/// Expected: UNSAT (asserting an invalid universally quantified formula).
///
/// CE lemma: NOT((e > 0) => (e > 1)) = (e > 0) AND NOT(e > 1)
///         = (e > 0) AND (e <= 1)
/// For integers: e >= 1 AND e <= 1, so e = 1. CE lemma is SAT with e=1.
/// Refinement should instantiate with x=1: (1 > 0) AND NOT(1 > 1) = counterexample.
#[test]
fn test_cegqi_arith_strict_boundary_refinement_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (=> (> x 0) (> x 1))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // INVALID formula — should be UNSAT.
    // If CEGQI refinement works correctly, it finds x=1 as counterexample
    // and the ground instance makes the system UNSAT.
    // If CEGQI is incomplete, this may return "unknown" — also acceptable.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Expected unsat or unknown for invalid forall with strict bounds, got: {outputs:?}",
    );
}
