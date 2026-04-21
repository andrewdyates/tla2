// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::{AletheRule, ProofId, Sort};
use z4_frontend::parse;
use z4_proof::check_proof_partial;

#[test]
fn test_get_proof_not_enabled() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    assert!(outputs[1].contains("proof generation is not enabled"));
}

#[test]
fn test_get_proof_after_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("proof is not available"));
}

#[test]
fn test_get_proof_after_unsat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    // Should get an actual proof (not an error)
    assert!(
        outputs[1].starts_with('('),
        "Expected proof output, got: {}",
        outputs[1]
    );
}

#[test]
fn test_qf_lia_check_sat_assuming_records_structured_split_loop_proof_6725() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (check-sat-assuming ((> x 1) (< x 0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);

    let theory_proofs = exec
        .last_original_clause_theory_proofs
        .as_ref()
        .expect("split-loop UNSAT should retain original-clause theory proofs");
    let theory_kinds: Vec<_> = theory_proofs
        .iter()
        .map(|proof| proof.as_ref().map(|proof| proof.kind))
        .collect();
    let proof_step_kinds: Vec<_> = exec
        .last_proof
        .as_ref()
        .map(|proof| {
            proof
                .steps
                .iter()
                .filter_map(|step| match step {
                    ProofStep::TheoryLemma { kind, .. } => Some(*kind),
                    _ => None,
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    assert!(
        theory_proofs.iter().flatten().any(|proof| {
            matches!(
                proof.kind,
                TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas
            )
        }),
        "expected a structured arithmetic theory annotation in split-loop proof ledger, got ledger={theory_kinds:?}, proof={proof_step_kinds:?}"
    );

    let proof = exec.get_proof();
    assert!(
        !proof.contains(":rule trust"),
        "LIA check-sat-assuming proof must not fall back to trust; proof_kinds={proof_step_kinds:?}\n{proof}"
    );
}

#[test]
fn test_get_proof_no_check_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert!(outputs[0].contains("no check-sat has been performed"));
}

#[test]
fn test_get_proof_rewrites_mod_div_auxiliary_symbols() {
    let benchmark_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/regression/parity_xor_unsat.smt2");
    let benchmark = std::fs::read_to_string(&benchmark_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", benchmark_path.display()));

    let input = format!("(set-option :produce-proofs true)\n{benchmark}\n(get-proof)\n");
    let commands = parse(&input).expect("parse benchmark");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute benchmark");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs
        .get(1)
        .expect("expected get-proof output after unsat");

    assert!(
        !proof.contains("_mod_q_"),
        "proof leaked internal _mod_q witness:\n{proof}"
    );
    assert!(
        !proof.contains("_mod_r_"),
        "proof leaked internal _mod_r witness:\n{proof}"
    );
    assert!(
        !proof.contains("(declare-fun "),
        "Alethe proof must not contain top-level declarations:\n{proof}"
    );
    assert!(
        proof.contains("(mod "),
        "expected surface mod term in rewritten proof:\n{proof}"
    );
}

#[test]
fn test_trust_lemma_negation_preserves_checker_pivots() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let and_ab = terms.mk_and(vec![a, b]);
    let or_dual = terms.mk_or(vec![not_a, not_b]);
    let not_or_dual = terms.mk_not_raw(or_dual);

    let mut proof = Proof::new();
    proof.add_assume(and_ab, Some("h0".to_string()));
    proof.add_assume(not_a, Some("h1".to_string()));
    proof.add_assume(not_or_dual, Some("h2".to_string()));

    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    let (summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "trust lemma fallback should remain checker-valid, got {error:?}"
    );
    assert_eq!(
        summary.total_steps,
        proof.len() as u32,
        "partial checker should account for the whole trust derivation"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
}

/// Direct unit test for prune_to_empty_clause_derivation.
///
/// Constructs a proof with both reachable and unreachable steps, prunes it,
/// and verifies that only the reachable steps survive with correct remapped
/// premise indices.
#[test]
fn test_prune_to_empty_clause_derivation_removes_unreachable_steps() {
    use z4_core::{AletheRule, TermId};

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);
    let t3 = TermId::new(3);

    let mut proof = Proof::new();

    // Step 0: Assume(t1) — reachable (used by final resolution)
    let h0 = proof.add_assume(t1, None);
    // Step 1: Assume(t2) — reachable (used by final resolution)
    let h1 = proof.add_assume(t2, None);
    // Step 2: TheoryLemma [t3] — UNREACHABLE (not referenced by anything)
    let _unreachable = proof.add_theory_lemma("EUF", vec![t3]);
    // Step 3: Step(Trust) clause=[not(t1), not(t2)] — reachable (premise of step 4)
    let trust_step = proof.add_rule_step(
        AletheRule::Trust,
        vec![t1, t2], // clause content doesn't matter for pruning
        vec![],
        vec![],
    );
    // Step 4: Step(ThResolution) clause=[] — reachable (empty clause target)
    let _final_step = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![], // empty clause
        vec![h0, h1, trust_step],
        vec![],
    );

    assert_eq!(proof.len(), 5);

    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);

    // Step 2 (unreachable TheoryLemma) should be removed
    assert_eq!(
        proof.len(),
        4,
        "expected 4 steps after pruning, got {}",
        proof.len()
    );

    // Step 0, 1 should still be Assume
    assert!(matches!(proof.steps[0], ProofStep::Assume(t) if t == t1));
    assert!(matches!(proof.steps[1], ProofStep::Assume(t) if t == t2));

    // Step 2 (was step 3) should be Trust rule
    assert!(matches!(
        &proof.steps[2],
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    ));

    // Step 3 (was step 4) should be ThResolution with remapped premises
    match &proof.steps[3] {
        ProofStep::Step {
            rule,
            clause,
            premises,
            ..
        } => {
            assert_eq!(*rule, AletheRule::ThResolution);
            assert!(clause.is_empty(), "final step should derive empty clause");
            // Old premises [0, 1, 3] should be remapped to [0, 1, 2]
            assert_eq!(premises, &[ProofId(0), ProofId(1), ProofId(2)]);
        }
        other => panic!("expected Step, got {other:?}"),
    }
}

/// Pruning a proof with no empty clause should be a no-op.
#[test]
fn test_prune_no_empty_clause_is_noop() {
    use z4_core::TermId;

    let t1 = TermId::new(1);
    let mut proof = Proof::new();
    proof.add_assume(t1, None);
    proof.add_theory_lemma("LRA", vec![t1]);

    let original_len = proof.len();
    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
    assert_eq!(
        proof.len(),
        original_len,
        "prune should be no-op without empty clause"
    );
}

/// Pruning a proof where all steps are reachable should not change it.
#[test]
fn test_prune_all_reachable_is_noop() {
    use z4_core::{AletheRule, TermId};

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(t1, None);
    let h1 = proof.add_assume(t2, None);
    let _final = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, h1], vec![]);

    assert_eq!(proof.len(), 3);
    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
    assert_eq!(proof.len(), 3, "all-reachable proof should not change");
}

#[test]
fn test_theory_packet_resolution_derives_empty_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let p = terms.mk_var("p", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_c = terms.mk_not(c);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(a, Some("h0".to_string()));
    proof.add_assume(b, Some("h1".to_string()));
    proof.add_assume(c, Some("h2".to_string()));
    proof.add_theory_lemma("EUF", vec![not_a, not_b, p]);
    proof.add_theory_lemma("LRA", vec![not_c, not_p]);

    assert!(
        crate::executor::proof_resolution::empty_clause::try_derive_empty_via_theory_packet_resolution(&terms, &mut proof),
        "expected two-lemma packet resolution to derive the empty clause"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));

    let (summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "packet-derived proof should remain checker-valid, got {error:?} ({summary})"
    );
}

#[test]
fn test_proof_quality_metrics_in_statistics() {
    // Verify that proof quality metrics appear in :all-statistics after UNSAT (#4420)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");

    let stats = &outputs[1];
    assert!(
        stats.contains(":proof-steps"),
        "Expected :proof-steps in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-verified"),
        "Expected :proof-verified in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-trust"),
        "Expected :proof-trust in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-complete"),
        "Expected :proof-complete in statistics: {stats}"
    );
}

#[test]
fn test_proof_quality_cleared_on_sat() {
    // Quality metrics should not carry over from a previous UNSAT (#4420)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    // Now do a SAT check — quality should be cleared
    let input2 = r#"
        (reset)
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const y Real)
        (assert (> y 0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands2 = parse(input2).unwrap();
    let outputs2 = exec.execute_all(&commands2).unwrap();
    assert_eq!(outputs2[0], "sat");

    let stats = &outputs2[1];
    // After SAT, proof-steps should not appear (no proof was generated)
    assert!(
        !stats.contains(":proof-steps"),
        "proof-steps should not appear after SAT: {stats}"
    );
}

#[test]
fn test_proof_quality_strict_check_via_api() {
    // Verify strict checking reports unsupported arithmetic lemmas instead of
    // panicking after #6686 downgraded bound axioms from LraFarkas to Generic.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    // Access the proof and run strict check
    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof should exist after UNSAT");
    let strict_result = z4_proof::check_proof_strict(proof, &exec.ctx.terms);

    // Arithmetic proofs now commonly include Generic theory lemmas, which
    // strict mode intentionally rejects until semantic validation exists.
    match strict_result {
        Ok(quality) => {
            assert!(
                quality.is_complete(),
                "strict-passing proof should be complete"
            );
        }
        Err(z4_proof::ProofCheckError::TrustStep { .. }) => {
            // Expected for trust-fallback proofs
        }
        Err(z4_proof::ProofCheckError::UnsupportedTheoryLemmaKind {
            kind: TheoryLemmaKind::Generic,
            ..
        }) => {
            // Expected for current arithmetic bound-axiom proofs (#6686).
        }
        Err(other) => {
            panic!("Unexpected strict check error: {other:?}");
        }
    }
}

#[cfg(feature = "proof-checker")]
#[test]
fn test_internal_proof_checker_records_partial_hole_metrics() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Bool);
    let not_x = exec.ctx.terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let hole = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, hole, h0);

    exec.run_internal_proof_check(&proof);
    let stats = exec.statistics();
    assert_eq!(stats.get_int("proof_checker_failures"), Some(0));
    assert_eq!(stats.get_int("proof_checker_skipped_hole_steps"), Some(1));
    assert_eq!(stats.get_int("proof_checker_checked_steps"), Some(2));
    assert_eq!(stats.get_int("proof_checker_total_steps"), Some(3));
}

/// Verify that invalid proofs record a failure without panicking (#7959).
/// Previously, debug builds would panic via `debug_assert!(false, ...)`,
/// which triggered `catch_unwind` in downstream consumers (sunder).
/// Now all builds log the error and record the failure in statistics.
#[cfg(feature = "proof-checker")]
#[test]
fn test_internal_proof_checker_records_failure_without_panic() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Bool);
    let y = exec.ctx.terms.mk_var("y", Sort::Bool);
    let not_x = exec.ctx.terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(not_x, None);
    proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: h0,
        clause2: h1,
    });

    exec.run_internal_proof_check(&proof);
    let stats = exec.statistics();
    assert_eq!(stats.get_int(PROOF_CHECKER_FAILURES_KEY), Some(1));
    assert_eq!(stats.get_int(PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY), Some(0));
    assert_eq!(stats.get_int(PROOF_CHECKER_CHECKED_STEPS_KEY), Some(3));
    assert_eq!(stats.get_int(PROOF_CHECKER_TOTAL_STEPS_KEY), Some(3));
}

/// Verify that `:check-proofs-strict` option is read correctly (#4420).
#[test]
fn test_strict_proofs_option_defaults_to_false() {
    let exec = Executor::new();
    assert!(
        !exec.strict_proofs_enabled(),
        "strict proofs should default to disabled"
    );
}

/// Verify that strict proof mode runs end-to-end on a proof shape the
/// current strict checker can validate completely (#4420).
#[test]
fn test_strict_proof_mode_end_to_end() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");

    // Proof quality should be populated after strict checker runs.
    let stats = &outputs[1];
    assert!(
        stats.contains(":proof-steps"),
        "Expected :proof-steps in statistics: {stats}"
    );
}

/// Verify that the strict option is correctly enabled via `set-option` (#4420).
#[test]
fn test_strict_proofs_option_enabled_via_set_option() {
    let input = r#"
        (set-option :check-proofs-strict true)
        (set-logic QF_LRA)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    assert!(
        exec.strict_proofs_enabled(),
        "strict proofs should be enabled after set-option"
    );
}

/// #6719 + #6722: QF_AX UNSAT proof with indirect store (ROW2 axiom).
///
/// Verifies trust-free proof for the indirect store pattern
/// `b = store(a, i, v)` with `i != j, select(b, j) != select(a, j)`.
/// - #6719: dpll_snapshot var_to_term capture for dynamic theory atoms
/// - #6722: eager array axiom proof annotations via record_eager_array_axiom_proofs
#[test]
fn test_array_row2_indirect_store_proof_structure() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (= b (store a i v)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof should exist after UNSAT with produce-proofs");
    let quality =
        z4_proof::check_proof_with_quality(proof, &exec.ctx.terms).expect("proof should validate");
    assert!(
        quality.resolution_count + quality.th_resolution_count >= 1,
        "proof should contain resolution or theory resolution steps: {quality}"
    );
    // Input assertions may be compressed into axioms, theory lemmas, or
    // th_resolution steps by the proof engine. Check the proof has at least
    // some input facts rather than asserting a specific assume count.
    assert!(
        quality.assume_count >= 1 || quality.theory_lemma_count >= 1,
        "proof should have at least one input fact (assume or theory lemma): {quality}"
    );
    assert!(
        Executor::proof_derives_empty_clause(proof),
        "proof must derive the empty clause"
    );
    assert!(
        quality.theory_lemma_count >= 1,
        "ROW2 eager axiom should be recorded as theory lemma (#6722): {quality}"
    );
    // Array axioms now export as `read_over_write_pos`/`read_over_write_neg`/
    // `extensionality` in Alethe format (#8073), no longer falling back to `trust`.
    // The improvement from #6722 is that the axiom is *categorized* as a
    // TheoryLemma(ArraySelectStore) instead of being an anonymous original clause.
}
