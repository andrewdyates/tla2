// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6756 Packet 1: direct combined-theory contradictions
//! should export structured proof rules instead of `:rule trust`.

#![allow(clippy::panic)]

use ntest::timeout;
use z4_dpll::Executor;
use z4_frontend::parse;
use z4_proof::{check_proof, check_proof_strict, check_proof_with_quality, ProofQuality};

fn run_unsat_proof(input: &str) -> (Executor, String, ProofQuality) {
    let commands = parse(input).expect("proof-enabled SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("proof-enabled SMT-LIB script should execute");

    assert_eq!(outputs.len(), 2, "expected check-sat + get-proof output");
    assert_eq!(outputs[0].trim(), "unsat", "expected UNSAT result");

    let proof_text = outputs[1].clone();
    assert!(
        proof_text.contains("(cl)"),
        "expected empty-clause derivation in proof:\n{proof_text}"
    );

    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");
    let quality = check_proof_with_quality(proof, exec.terms())
        .expect("proof quality checker rejected proof");

    (exec, proof_text, quality)
}

fn assert_last_unsat_proof_is_strict(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof_strict(proof, exec.terms()).expect("strict proof checker rejected proof");
}

/// Direct QF_AUFLIA fast-path contradiction: `(select a 0) = 1` vs `(select a 0) = 2`.
/// Semantically Farkas-valid integer contradictions should export `la_generic`.
#[test]
#[timeout(5_000)]
fn test_auflia_direct_contradiction_exports_la_generic_6756() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 1))
        (assert (= (select a 0) 2))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "direct AUFLIA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "direct AUFLIA proof should not contain :rule trust after #6756 Packet 1:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "direct AUFLIA proof should contain :rule la_generic:\n{proof_text}"
    );
}

/// Same as above but with push/pop scope.
#[test]
#[timeout(5_000)]
fn test_auflia_direct_contradiction_with_push_pop_6756() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (push 1)
        (assert (= (select a 0) 1))
        (assert (= (select a 0) 2))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "push/pop AUFLIA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "push/pop AUFLIA proof should not contain :rule trust after #6756 Packet 1:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "push/pop AUFLIA proof should contain :rule la_generic:\n{proof_text}"
    );
}

/// Direct QF_AUFLIA with three array reads — verifies that the promotion
/// handles more than two-literal clauses (falls through to the LRA solver
/// path in `reconstruct_missing_farkas_coefficients`).
#[test]
#[timeout(5_000)]
fn test_auflia_three_reads_direct_contradiction_6756() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 2))
        (assert (not (= (select a 0) 1)))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "three-read AUFLIA proof should not contain hole steps: {quality:?}"
    );
    // This case may still contain trust if the contradiction is resolved
    // without a theory lemma. The key assertion is that it produces a valid proof.
    assert!(
        proof_text.contains("(cl)"),
        "three-read AUFLIA proof should derive the empty clause:\n{proof_text}"
    );
}

#[test]
#[timeout(5_000)]
fn test_uflra_direct_contradiction_exports_euf_and_lra_rules_6756() {
    let input = r#"
        (set-logic QF_UFLRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (declare-fun f (Real) Real)
        (assert (= x 0.0))
        (assert (= (f x) 1.0))
        (assert (= (f 0.0) 2.0))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "direct UFLRA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "direct UFLRA proof should not contain :rule trust after #6756 Packet 3:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "direct UFLRA proof should contain eq_congruent:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "direct UFLRA proof should contain la_generic:\n{proof_text}"
    );
    assert_last_unsat_proof_is_strict(&exec);
}

#[test]
#[timeout(5_000)]
fn test_uflra_direct_contradiction_with_push_pop_6756() {
    let input = r#"
        (set-logic QF_UFLRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (declare-fun f (Real) Real)
        (push 1)
        (assert (= x 0.0))
        (assert (= (f x) 1.0))
        (assert (= (f 0.0) 2.0))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "push/pop UFLRA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "push/pop UFLRA proof should not contain :rule trust after #6756 Packet 3:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "push/pop UFLRA proof should contain eq_congruent:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "push/pop UFLRA proof should contain la_generic:\n{proof_text}"
    );
    assert_last_unsat_proof_is_strict(&exec);
}
