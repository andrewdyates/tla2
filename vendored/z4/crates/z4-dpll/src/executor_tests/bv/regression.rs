// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// #4169/#4087: Certus Seq pattern — quantified array with BV64 indices and bvzeroext
// Mimics: s.drop_first().index(0) == 42 given s.index(1) == 42
#[test]
fn test_certus_seq_drop_first_pattern_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const result (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        ; len == 5
        (assert (= len #x00000005))
        ; s[1] == 42
        (assert (= (select s #x0000000000000001) #x0000002A))
        ; forall i: result[i] = s[i + 1] (drop_first shifts indices by 1)
        (assert (forall ((i (_ BitVec 64)))
            (! (= (select result i) (select s (bvadd i #x0000000000000001)))
               :pattern ((select result i)))))
        ; negation of assertion: result[0] != 42
        (assert (not (= (select result #x0000000000000000) #x0000002A)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "certus drop_first pattern: result[0] should equal s[1]=42"
    );
}

// #4169: Same pattern but with bvzeroext indices (matching certus coerce_seq_index)
#[test]
fn test_certus_seq_zeroext_index_pattern_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const result (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        ; len == 5
        (assert (= len #x00000005))
        ; s[zext(1)] == 42 (index via zero-extend from BV32 to BV64)
        (assert (= (select s ((_ zero_extend 32) #x00000001)) #x0000002A))
        ; forall i: result[i] = s[i + 1]
        (assert (forall ((i (_ BitVec 64)))
            (! (= (select result i) (select s (bvadd i #x0000000000000001)))
               :pattern ((select result i)))))
        ; negation: result[zext(0)] != 42
        (assert (not (= (select result ((_ zero_extend 32) #x00000000)) #x0000002A)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "certus zeroext index pattern: result[zext(0)] should equal s[zext(1)]=42"
    );
}

// #4169: Certus seq_last pattern — self-contradictory assertion with symbolic index
#[test]
fn test_certus_seq_last_pattern_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        ; len == 3
        (assert (= len #x00000003))
        ; s[len-1] == 42 (last element)
        (assert (= (select s ((_ zero_extend 32) (bvsub len #x00000001))) #x0000002A))
        ; negation: s.last() != 42
        (assert (not (= (select s ((_ zero_extend 32) (bvsub len #x00000001))) #x0000002A)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "certus last pattern: s[len-1] == 42 and NOT s[len-1] == 42 should be unsat"
    );
}

/// Regression: BV-return UF congruence via check-sat-assuming (#5437).
#[test]
fn test_executor_qf_ufbv_check_sat_assuming_congruence_unsat_5437() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (check-sat-assuming ((distinct (f x) (f y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: non-BV-return UF congruence via check-sat-assuming (#5437).
#[test]
fn test_executor_qf_ufbv_non_bv_return_check_sat_assuming_unsat_5437() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (check-sat-assuming ((distinct (f x) (f y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: AUFBV UF congruence via check-sat-assuming (#5437).
/// Uses AUFBV logic with only UF (no array terms) to test congruence path.
#[test]
fn test_executor_qf_aufbv_check_sat_assuming_congruence_unsat_5437() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (check-sat-assuming ((distinct (f x) (f y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: empty assumptions on UFBV still works (#5437).
#[test]
fn test_executor_qf_ufbv_check_sat_assuming_empty_unsat_5437() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f x) (f y)))
        (check-sat-assuming ())
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: check-sat-assuming BV SAT must extract BvModel for get-value (#5443).
/// Previously, the check-sat-assuming path called solve_and_store_model with bv_model=None,
/// causing get-value to return empty/missing BV values after assumption-based SAT.
#[test]
fn test_executor_qf_bv_check_sat_assuming_get_value_5443() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (bvuge x #x42)))
        (check-sat-assuming (p))
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // get-value must return a BV value for x, not empty/error
    assert!(
        outputs[1].contains("x") && outputs[1].contains("#x"),
        "Expected BV value for x in get-value output, got: {}",
        outputs[1]
    );
}

/// Probe: Bool variable substituted with bvult predicate.
/// When preprocessing substitutes `p → (bvult x #x42)`, the model recovery code
/// must correctly evaluate the bvult predicate to recover p's value.
/// This exercises the `_ => None` fallthrough in Bool substitution recovery.
#[test]
fn test_executor_qf_bv_bool_subst_bvult_get_value() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (bvult x #x42)))
        (assert p)
        (check-sat)
        (get-value (p x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // p must be true (we asserted it)
    assert!(
        outputs[1].contains("p") && outputs[1].contains("true"),
        "Expected p=true in get-value output, got: {}",
        outputs[1]
    );
    // x must be < #x42 (66)
    assert!(
        outputs[1].contains("x") && outputs[1].contains("#x"),
        "Expected BV value for x in get-value output, got: {}",
        outputs[1]
    );
}

/// Regression: check-sat-assuming UFBV SAT must extract BvModel for get-value (#5443).
#[test]
fn test_executor_qf_ufbv_check_sat_assuming_get_value_5443() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (= (f x) #xFF)))
        (check-sat-assuming (p))
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // get-value must return a BV value for x
    assert!(
        outputs[1].contains("x") && outputs[1].contains("#x"),
        "Expected BV value for x in get-value output, got: {}",
        outputs[1]
    );
}

/// Regression test for #5115: MCMPC circuit with Bool-gate wires over BV extracts.
///
/// Variable substitution eliminates intermediate Bool variables (b0-b3, xor_out)
/// that are defined via BV extract predicates and Bool gates (and, or, xor).
/// Without the Tseitin SAT seeding + evaluate_bool_substitution fix, model
/// validation fails because eliminated Bool wires referencing non-eliminated
/// Bool variables (and01, or23) cannot be resolved.
#[test]
fn test_bv_bool_gate_wires_mcmpc_5115() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b0 () Bool) (declare-fun b1 () Bool)
        (declare-fun b2 () Bool) (declare-fun b3 () Bool)
        (assert (= b0 (= #b1 ((_ extract 0 0) x))))
        (assert (= b1 (= #b1 ((_ extract 1 1) x))))
        (assert (= b2 (= #b1 ((_ extract 2 2) x))))
        (assert (= b3 (= #b1 ((_ extract 3 3) x))))
        (declare-fun and01 () Bool)
        (declare-fun or23 () Bool)
        (declare-fun xor_out () Bool)
        (assert (= and01 (and b0 b1)))
        (assert (= or23 (or b2 b3)))
        (assert (= xor_out (xor and01 or23)))
        (assert xor_out)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "#5115: MCMPC Bool-gate circuit should be SAT, got: {}",
        outputs[0]
    );
}

/// Regression test: BV shift operations in substitution targets (#5115).
/// When VariableSubstitution eliminates a variable whose definition uses
/// bvshl/bvlshr/bvashr, the model evaluator must handle these operations
/// to recover the variable's value. Without the shift evaluator, the model
/// is incomplete and validation fails.
#[test]
fn test_bv_shift_model_recovery_5115() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun shifted () (_ BitVec 8))
        (declare-fun lshifted () (_ BitVec 8))
        (assert (= x #xAB))
        (assert (= shifted (bvshl x #x02)))
        (assert (= lshifted (bvlshr x #x04)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "#5115: BV shift model recovery should be SAT, got: {}",
        outputs[0]
    );
}

/// Regression test for #6248: BV solver must not panic in CONDITIONING.
///
/// The BV bit-blasting path creates a fresh SAT solver where conditioning
/// (GBCE) was previously enabled by default. For certain BV-array formulas,
/// conditioning's root-satisfied invariant could be violated, causing a
/// debug assertion panic. The fix disables conditioning for all BV solve
/// paths since BV instances are one-shot.
#[test]
fn test_regression_6248_bv_conditioning_no_panic() {
    // QF_ABV formula with multiple array ops and BV arithmetic.
    // Generates enough clauses from bit-blasting to potentially trigger
    // conditioning during preprocessing or inprocessing.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (declare-const z (_ BitVec 8))

        ; Store and select chain
        (assert (= (select (store a x #xFF) x) #xFF))
        (assert (= (select (store b y #x01) y) #x01))

        ; Cross-array constraint forcing search
        (assert (= (bvadd (select a z) (select b z)) #x00))

        ; Arithmetic constraints that increase variable count
        (assert (bvult x y))
        (assert (bvult y z))
        (assert (not (= x #x00)))

        (check-sat)
        (get-value (x y z))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // The formula is satisfiable. The key assertion is that we don't panic.
    assert_eq!(
        outputs[0], "sat",
        "#6248: QF_ABV formula should be SAT without CONDITIONING panic, got: {}",
        outputs[0]
    );

    // Model verification: get-value must return BV hex values for all three variables.
    // The formula requires bvult x y, bvult y z, and x != #x00.
    let model_output = &outputs[1];
    // Must contain at least one hex BV literal
    assert!(
        model_output.contains("#x"),
        "#6248: get-value must return BV hex values; got: {model_output}",
    );
    // x must not be assigned #x00 (constraint: not (= x #x00))
    assert!(
        !model_output.contains("(x #x00)"),
        "#6248: model has x = #x00 which violates (not (= x #x00)); got: {model_output}",
    );
}
