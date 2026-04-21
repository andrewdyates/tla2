// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the consumer-facing proof artifact API (#6354).
//!
//! Verifies that `export_last_unsat_artifact` returns correct quality metrics
//! and lean5 compatibility flags for pure Boolean, QF_UF, and arithmetic cases.

use crate::api::proofs::strict_verdict_from_result;
use crate::api::*;

/// pure Boolean contradiction: p AND NOT p.
/// The proof should be trust-free and lean5-supported.
#[test]
fn artifact_qf_bool_accepts_strict_and_lean5() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "pure Boolean proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        artifact.lean5_supported,
        "pure Boolean proof must be lean5-supported: {}",
        artifact.quality,
    );
    assert!(
        artifact
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "pure Boolean artifact should carry non-empty LRAT bytes",
    );
    assert!(
        artifact.farkas_certificates.is_empty(),
        "pure Boolean proof should not export Farkas certificates",
    );
    match &artifact.strict_verdict {
        StrictProofVerdict::Verified(quality) => {
            assert!(
                quality.is_complete(),
                "pure Boolean strict proof must remain complete: {quality}",
            );
        }
        StrictProofVerdict::Rejected(reason) => {
            panic!("pure Boolean proof must pass strict validation, got: {reason}");
        }
    }
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "pure Boolean artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Lean5),
        Ok(()),
        "pure Boolean artifact should be acceptable in lean5 mode",
    );
}

/// Simple QF_UF contradiction: a=b, b=c, NOT(a=c).
/// The proof should be trust-free and lean5-supported.
///
/// Uses `parse_smtlib2` to declare an uninterpreted sort, since the Rust API
/// does not yet expose `declare_sort`.
#[test]
fn artifact_qf_uf_accepts_strict_and_lean5() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    solver
        .parse_smtlib2(
            r#"
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun c () U)
            (assert (= a b))
            (assert (= b c))
            (assert (not (= a c)))
            "#,
        )
        .expect("SMT-LIB2 parsing should succeed");

    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "QF_UF proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        artifact.lean5_supported,
        "simple QF_UF proof must be lean5-supported: {}",
        artifact.quality,
    );
    assert!(
        matches!(
            &artifact.strict_verdict,
            StrictProofVerdict::Verified(quality) if quality.is_complete()
        ),
        "QF_UF proof must export a successful strict verdict: {:?}",
        artifact.strict_verdict,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "QF_UF artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Lean5),
        Ok(()),
        "QF_UF artifact should be acceptable in lean5 mode",
    );
}

/// Simple QF_LRA contradiction: x > 0 AND x < 0.
///
/// The proof should pass strict checking, but lean5 support is currently
/// limited to a strict subset that excludes arithmetic theory lemmas.
#[test]
fn artifact_qf_lra_strict_but_not_lean5() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLra);
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Real);
    let zero = solver.real_const(0.0);
    let gt_term = solver.gt(x, zero);
    solver.assert_term(gt_term);
    let lt_term = solver.lt(x, zero);
    solver.assert_term(lt_term);

    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "LRA proof must export a successful strict verdict: {:?}",
        artifact.strict_verdict,
    );
    assert!(
        !artifact.lean5_supported,
        "LRA proof should remain outside the lean5-supported subset",
    );
    assert!(
        artifact
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "LRA artifact should carry non-empty LRAT bytes",
    );
    assert!(
        !artifact.farkas_certificates.is_empty(),
        "LRA artifact should export Farkas certificates",
    );
    assert!(
        artifact
            .farkas_certificates
            .iter()
            .all(|certificate| !certificate.coefficients.is_empty()),
        "exported Farkas certificates should contain coefficients",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "LRA artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Lean5),
        Err(ProofAcceptanceError::NotLean5Supported),
        "LRA artifact should be rejected in lean5 mode",
    );
}

/// SAT result returns None for the proof artifact.
#[test]
fn artifact_sat_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None after SAT result"
    );
}

/// Proofs disabled returns None for the proof artifact.
#[test]
fn artifact_proofs_disabled_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    // Proofs disabled by default.

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None when proofs not enabled"
    );
}

/// Individual proof accessor: export_last_proof_alethe returns non-empty text.
#[test]
fn alethe_export_returns_text() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let alethe = solver
        .export_last_proof_alethe()
        .expect("Alethe text must be present");
    assert!(!alethe.is_empty());
    // Alethe proofs contain assume and step/resolution commands
    assert!(
        alethe.contains("assume") || alethe.contains("step"),
        "Alethe text should contain proof commands"
    );
}

/// Individual proof accessor: last_proof_quality returns metrics.
#[test]
fn quality_accessor_returns_metrics() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let quality = solver
        .last_proof_quality()
        .expect("quality must be present");
    assert!(quality.total_steps > 0);
    assert!(quality.is_complete());
}

/// Negative regression: a whitelisted rule (AllSimplify) that derives an
/// incorrect clause must be rejected by the strict gate even though the
/// diagnostic quality says "complete" and the rule whitelist accepts it.
///
/// This is the key #6541 regression: before the strict gate, this proof would
/// have been lean5_supported=true because `trust_count == 0`, `hole_count == 0`,
/// and AllSimplify is in the whitelist. Now lean5_supported requires
/// check_proof_strict to succeed, which rejects unvalidated generic rules.
#[test]
fn strict_rejection_is_preserved_on_artifact_boundary() {
    use z4_core::{AletheRule, Proof, Sort as CoreSort, TermStore};
    use z4_proof::{check_proof_strict, check_proof_with_quality};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", CoreSort::Bool);
    let not_x = terms.mk_not(x);

    // Build a bogus proof:
    //   assume x
    //   AllSimplify deriving (not x) — this is semantically wrong
    //   resolution on x to derive empty clause
    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let bogus = proof.add_rule_step(AletheRule::AllSimplify, vec![not_x], Vec::new(), Vec::new());
    proof.add_resolution(vec![], x, h0, bogus);

    // Diagnostic (non-strict) quality should say "complete" —
    // no trust, no hole, the proof derives the empty clause.
    let diag = check_proof_with_quality(&proof, &terms)
        .expect("non-strict check should accept this proof");
    assert!(
        diag.is_complete(),
        "diagnostic quality should be complete (no trust/hole): {diag}"
    );

    // Strict checker rejects: AllSimplify is not semantically validated.
    let strict_error = check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject bogus AllSimplify");
    let strict_error_text = strict_error.to_string();
    let strict_verdict = strict_verdict_from_result(Err(strict_error));
    assert_eq!(
        strict_verdict,
        StrictProofVerdict::Rejected(strict_error_text),
        "artifact boundary must preserve the strict rejection explanation",
    );
}
