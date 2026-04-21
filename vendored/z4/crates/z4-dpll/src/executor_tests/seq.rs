// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence theory executor-level regression tests (#6486).
//!
//! Tests that Seq-sorted queries return correct results after the
//! `skip_model_eval` fix. Without this fix, unconstrained Seq variables
//! get no model value and `finalize_sat_model_validation()` degrades
//! SAT to Unknown.

use crate::Executor;
use z4_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

// ---------------------------------------------------------------------------
// Regression: #6486 — Seq equality on fresh variables returns Unknown
// ---------------------------------------------------------------------------

/// Two fresh Seq(Int) variables asserted equal must be SAT.
/// Before #6486 fix, this returned Unknown because extract_model()
/// could not concretize unconstrained Seq variables.
#[test]
fn test_seq_eq_fresh_variables_is_sat_6486() {
    let smt = r#"
(set-logic QF_SEQ)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(assert (= a b))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "Seq(Int) equality on fresh variables: expected sat, got: {result}"
    );
}

/// Two fresh Seq(Int) variables asserted distinct must be SAT.
#[test]
fn test_seq_distinct_fresh_variables_is_sat_6486() {
    let smt = r#"
(set-logic QF_SEQ)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(assert (distinct a b))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "Seq(Int) distinct on fresh variables: expected sat, got: {result}"
    );
}

/// Seq(Int) variable equated to seq.unit of unconstrained Int must be SAT.
/// This exercises the SeqLIA path since `seq.unit` plus Int elements routes
/// through the combined EUF+Seq+LIA solver.
#[test]
fn test_seq_unit_variable_element_is_sat_6486() {
    let smt = r#"
(set-logic QF_SEQLIA)
(declare-const a (Seq Int))
(declare-const x Int)
(assert (= a (seq.unit x)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "Seq(Int) eq seq.unit(x): expected sat, got: {result}"
    );
}
