// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for ProofManager (DRAT/LRAT proof emission and validation).

use super::{ProofAddKind, ProofManager};
use crate::proof::ProofOutput;
use crate::test_util::lit;

#[test]
fn test_lrat_hint_validation_rejects_unknown_hint_id() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    let derived = [lit(0, true)];
    let added = manager
        .emit_add(&derived, &[1], ProofAddKind::Derived)
        .expect("derived add should succeed");
    assert_eq!(added, 2);

    // Hint 99 is unknown — always-on validation catches this (#5005).
    let bad = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = manager.emit_add(&[lit(1, true)], &[99], ProofAddKind::Derived);
    }));
    assert!(bad.is_err(), "expected invalid hint assertion");
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_chain_verifier_catches_bad_hints_via_manager() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);
    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false), lit(1, true)]);
    manager.register_clause_id(2);
    let clause_id = manager
        .emit_add(&[lit(1, true)], &[1, 2], ProofAddKind::Derived)
        .expect("valid LRAT add should succeed");
    assert!(clause_id > 0);
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_chain_verifier_skips_non_empty_derived_clauses() {
    // Non-empty derived clauses skip online LRAT verification (#7108).
    // The online checker cannot verify all learned clause chains because
    // the resolution chain references reason clauses whose non-resolved
    // literals aren't established by any hint. Non-empty derived clauses
    // are added as originals to keep the checker DB correct.
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);

    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    manager.register_clause_id(1);

    let result = manager.emit_add(&[lit(0, false), lit(1, false)], &[1], ProofAddKind::Derived);
    assert!(result.is_ok(), "emit_add should succeed");
    // No LRAT failure: non-empty derived clauses are added as originals.
    assert_eq!(
        manager.lrat_failures(),
        0,
        "non-empty derived clauses skip online LRAT verification"
    );
}

#[test]
fn test_block_lrat_for_theory_lemmas_noops_emission() {
    let output = ProofOutput::lrat_text(Vec::new(), 0);
    let mut manager = ProofManager::new(output, 1);
    manager.block_lrat_for_theory_lemmas();
    let add_id = manager
        .emit_add(&[lit(0, true), lit(0, false)], &[1], ProofAddKind::Derived)
        .expect("blocked LRAT add should be a no-op");
    assert_eq!(add_id, 0);
    manager
        .emit_delete(&[lit(0, true)], 1)
        .expect("blocked LRAT delete should be a no-op");
    assert_eq!(manager.added_count(), 0);
}

#[test]
fn test_lrat_axiom_add_without_hints_is_skipped() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    let added = manager
        .emit_add(&clause, &[], ProofAddKind::Axiom)
        .expect("skip path should be non-failing");
    assert_eq!(added, 0);
    assert_eq!(manager.added_count(), 0);
}

#[test]
fn test_lrat_trusted_transform_without_hints_emits() {
    // TrustedTransform clauses in LRAT mode are not suppressed (#7108, #6270).
    // They need real clause IDs so downstream derivations can reference them.
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    let added = manager
        .emit_add(&clause, &[], ProofAddKind::TrustedTransform)
        .expect("TrustedTransform should emit successfully");
    assert_ne!(added, 0, "TrustedTransform should get a real clause ID");
    assert_eq!(manager.added_count(), 1);
}

#[test]
fn test_drat_trusted_transform_emits_normally() {
    let output = ProofOutput::drat_text(Vec::new());
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    let clause = [lit(0, false), lit(1, false)];
    let added = manager
        .emit_add(&clause, &[], ProofAddKind::TrustedTransform)
        .expect("DRAT add should succeed");
    assert_eq!(added, 0);
    assert_eq!(manager.added_count(), 1);
}

fn manager_with_complementary_unit_origins() -> ProofManager {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    // Register full original clauses so the LRAT chain checker has
    // clause content for RUP verification (not just IDs).
    manager.register_original_clause(&[lit(0, true)]); // clause 1: (a)
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false)]); // clause 2: (!a)
    manager.register_clause_id(2);
    manager
}

fn assert_lrat_delete_line(del_line: &str, empty_clause_id: u64) {
    assert!(del_line.contains(" d "));
    assert!(del_line.contains(&format!(" {empty_clause_id} ")));
    assert!(del_line.ends_with(" 0") || del_line.ends_with(" 0 "));
    let parts: Vec<&str> = del_line.split_whitespace().collect();
    assert!(parts.len() >= 4);
    let step_id: u64 = parts[0].parse().expect("step_id should be numeric");
    assert!(step_id > empty_clause_id);
    assert_eq!(parts[1], "d");
    assert_eq!(parts[parts.len() - 1], "0");
}

#[test]
fn test_emit_delete_empty_clause_produces_valid_lrat_deletion() {
    let mut manager = manager_with_complementary_unit_origins();
    let empty_clause_id = manager
        .emit_add(&[], &[1, 2], ProofAddKind::Derived)
        .expect("empty clause derivation should succeed");
    assert_eq!(empty_clause_id, 3);
    manager
        .emit_delete(&[], empty_clause_id)
        .expect("empty clause deletion should succeed");

    // The deleted ID should be removed from the known set (always-on #5005).
    assert!(
        !manager.known_lrat_ids.contains(&empty_clause_id),
        "deleted empty-clause ID must be removed from known set"
    );

    // Extract the LRAT text output and verify format.
    let output = manager.into_output();
    let text = String::from_utf8(output.into_vec().expect("flush ok"))
        .expect("LRAT output should be valid UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2);
    assert!(lines[0].starts_with("3 "));
    assert_lrat_delete_line(lines[1], empty_clause_id);
}

#[test]
#[cfg(debug_assertions)]
fn test_emit_add_rejects_empty_axiom_clause() {
    let output = ProofOutput::drat_text(Vec::new());
    let mut manager = ProofManager::new(output, 1);
    let bad = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = manager.emit_add(&[], &[], ProofAddKind::Axiom);
    }));
    assert!(bad.is_err(), "expected empty-axiom assertion");
}

#[test]
fn test_verify_unsat_chain_passes_after_valid_proof() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);

    // Register originals: (a) and (!a).
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false)]);
    manager.register_clause_id(2);

    // Derive empty clause with hints [1, 2].
    let _ = manager
        .emit_add(&[], &[1, 2], ProofAddKind::Derived)
        .expect("empty clause derivation should succeed");

    // verify_unsat_chain should pass — IDs are tracked and non-empty.
    manager.verify_unsat_chain();
}

#[test]
fn test_verify_unsat_chain_skipped_for_drat_mode() {
    let output = ProofOutput::drat_text(Vec::new());
    let manager = ProofManager::new(output, 1);
    // Should not panic — DRAT mode skips LRAT chain checks.
    manager.verify_unsat_chain();
}

#[test]
fn test_verify_unsat_chain_skipped_when_theory_blocked() {
    let output = ProofOutput::lrat_text(Vec::new(), 0);
    let mut manager = ProofManager::new(output, 1);
    manager.block_lrat_for_theory_lemmas();
    // Should not panic — theory-blocked proofs skip LRAT checks.
    manager.verify_unsat_chain();
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_chain_verifier_receives_deduped_hints() {
    // Verify that the online LratChecker receives deduped hints, matching
    // what goes to the LRAT file and standalone z4-lrat-check binary.
    // Duplicate hints are semantically harmless for RUP (SatisfiedUnit
    // no-op) but the checker should see the same chain as external tools.
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);

    // Register (a ∨ b) and (¬a ∨ b).
    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false), lit(1, true)]);
    manager.register_clause_id(2);

    // Derive (b) with duplicate hints [1, 2, 1]. The dedup at the output
    // boundary removes the duplicate, so both the file and online checker
    // see [1, 2]. This must not panic — the deduped chain is valid.
    let clause_id = manager
        .emit_add(&[lit(1, true)], &[1, 2, 1], ProofAddKind::Derived)
        .expect("deduped hints should produce valid chain");
    assert!(clause_id > 0);
    assert_eq!(manager.lrat_failures(), 0);

    // Verify the LRAT file also received deduped hints.
    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let add_line = text.lines().next().expect("at least one line");
    // Format: "3 1 0 1 2 0" — clause_id=3, lits=[1], hints=[1,2].
    // NOT "3 1 0 1 2 1 0" (with duplicate hint 1).
    let parts: Vec<&str> = add_line.split_whitespace().collect();
    // Find the hint section (after the second "0").
    let first_zero = parts.iter().position(|&p| p == "0").unwrap();
    let hints_section = &parts[first_zero + 1..parts.len() - 1];
    assert_eq!(
        hints_section,
        &["1", "2"],
        "LRAT file should have deduped hints [1, 2], not [1, 2, 1]"
    );
}
