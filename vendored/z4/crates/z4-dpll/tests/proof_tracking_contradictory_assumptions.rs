// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

use ntest::timeout;
use z4_core::{AletheRule, ProofStep};
use z4_dpll::Executor;
use z4_frontend::parse;
use z4_proof::{check_proof, check_proof_strict, ProofQuality};

fn assert_last_unsat_proof_is_valid(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof(proof, exec.terms())
        .expect("internal proof checker rejected proof for UNSAT result");
}

fn assert_last_unsat_proof_strict(exec: &Executor) -> ProofQuality {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof_strict(proof, exec.terms()).expect("strict proof checker rejected proof")
}

#[test]
#[timeout(5_000)]
fn test_check_sat_assuming_contradictory_assumptions_emits_resolution_contradiction() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (check-sat-assuming (a (not a)))
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let internal_proof = exec
        .last_proof()
        .expect("expected proof object for contradictory assumptions");
    assert!(
        internal_proof
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::TheoryLemma { .. })),
        "expected contradictory assumptions to avoid theory lemmas, got {:?}",
        internal_proof.steps
    );
    assert!(
        internal_proof.steps.iter().all(|step| {
            !matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    ..
                }
            )
        }),
        "expected direct SAT resolution path, found th_resolution in {:?}",
        internal_proof.steps
    );
    assert!(
        matches!(
            internal_proof.steps.last(),
            Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
        ),
        "expected final empty-clause resolution step, got {:?}",
        internal_proof.steps.last()
    );

    let proof = &outputs[1];
    assert!(
        proof.matches("(assume ").count() >= 2,
        "expected assumption steps for contradictory assumptions, got:\n{proof}"
    );
    assert!(
        proof.contains(":rule resolution"),
        "expected direct resolution for contradictory assumptions:\n{proof}"
    );
    assert!(
        !proof.contains(":rule th_resolution"),
        "expected contradictory assumptions to avoid th_resolution fallback:\n{proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "expected empty clause contradiction in proof:\n{proof}"
    );
}
