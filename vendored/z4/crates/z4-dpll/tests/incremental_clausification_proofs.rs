// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use z4_dpll::Executor;
use z4_frontend::parse;
use z4_proof::check_proof;

fn assert_last_unsat_proof_is_valid(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof(proof, exec.terms())
        .expect("internal proof checker rejected proof for UNSAT result");
}

fn assert_incremental_unsat_proof(exec: &Executor, outputs: &[String], label: &str) {
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    let proof = &outputs[1];
    assert!(
        proof.contains(":rule or_pos"),
        "expected :rule or_pos in {label} incremental proof:\n{proof}"
    );
    assert!(
        !proof.contains(":rule hole"),
        "{label} incremental proof should not contain :rule hole:\n{proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in {label} incremental proof:\n{proof}"
    );
    assert_last_unsat_proof_is_valid(exec);
}

/// Standalone QF_LRA proof mode must route through the incremental split-loop
/// path and preserve incremental clausification proof steps (#6660).
#[test]
#[timeout(10_000)]
fn test_standalone_expression_split_clausification_proofs_are_exported() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const gate Bool)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (assert (= x 1.0))
        (assert (= y 0.0))
        (assert (= z 1.0))
        (assert (not gate))
        (assert (or gate (not (= (+ x y) z))))
        (check-sat)
        (get-proof)
    "#;

    let mut exec = Executor::new();
    let commands = parse(input).expect("parse standalone expression-split input");
    let outputs = exec
        .execute_all(&commands)
        .expect("execute standalone expression-split input");
    assert_incremental_unsat_proof(&exec, &outputs, "standalone expression-split");
}
