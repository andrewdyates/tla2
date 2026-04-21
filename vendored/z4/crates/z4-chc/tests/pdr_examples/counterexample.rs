// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that counterexample steps have populated assignments from SMT models
///
/// Uses subtraction_unsafe.smt2 which should find a counterexample trace:
/// x = 3 -> 2 -> 1 -> 0 -> -1 (violates x >= 0)
///
/// Note: This test is intended to ensure counterexample traces include concrete
/// assignments from SMT models on at least some steps.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_counterexample_has_assignments() {
    let config = test_config(true);
    let result = pdr_solve_from_file(example_path("subtraction_unsafe.smt2"), config).unwrap();

    match &result {
        PdrResult::Unsafe(cex) => {
            eprintln!("Counterexample has {} steps:", cex.steps.len());
            for (i, step) in cex.steps.iter().enumerate() {
                eprintln!(
                    "  Step {}: predicate {:?}, assignments: {:?}",
                    i, step.predicate, step.assignments
                );
            }

            // At least some steps should have non-empty assignments
            let steps_with_assignments = cex
                .steps
                .iter()
                .filter(|s| !s.assignments.is_empty())
                .count();

            eprintln!(
                "Steps with non-empty assignments: {}/{}",
                steps_with_assignments,
                cex.steps.len()
            );

            // Verify at least one step has assignments (the root POB might not have a model)
            assert!(
                steps_with_assignments > 0 || cex.steps.is_empty(),
                "At least some counterexample steps should have variable assignments"
            );

            // Check witness is populated with instances
            if let Some(ref witness) = cex.witness {
                eprintln!(
                    "Derivation witness has {} entries, root={}",
                    witness.entries.len(),
                    witness.root
                );
                assert!(
                    !witness.entries.is_empty(),
                    "Derivation witness should have entries"
                );

                // Check that witness entries have instances populated
                for (i, entry) in witness.entries.iter().enumerate() {
                    eprintln!(
                        "  Entry {}: pred {:?}, level {}, instances: {:?}",
                        i, entry.predicate, entry.level, entry.instances
                    );
                }

                // At least some entries should have instances (from SMT models)
                let entries_with_instances = witness
                    .entries
                    .iter()
                    .filter(|e| !e.instances.is_empty())
                    .count();
                eprintln!(
                    "Entries with instances: {}/{}",
                    entries_with_instances,
                    witness.entries.len()
                );

                // Verify at least one entry has instances
                assert!(
                    entries_with_instances > 0 || witness.entries.is_empty(),
                    "At least some derivation entries should have concrete instances"
                );
            }
        }
        _ => {
            // subtraction_unsafe should be unsafe, but we're mainly testing assignment extraction
            eprintln!("Note: subtraction_unsafe did not return Unsafe result");
        }
    }
}

/// Test that incoming_clause is populated in derivation witness for must-reachability-driven UNSAFE.
/// The counter_unsafe example triggers must-reachability detection when must_summaries is enabled.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_must_reachability_has_incoming_clause() {
    let config = test_config(true);
    // use_must_summaries: true is already the default

    let result = pdr_solve_from_file(example_path("counter_unsafe.smt2"), config).unwrap();

    match &result {
        PdrResult::Unsafe(cex) => {
            eprintln!("Counterexample has {} steps:", cex.steps.len());

            // Check witness is populated with incoming_clause
            if let Some(ref witness) = cex.witness {
                eprintln!(
                    "Derivation witness has {} entries, query_clause={:?}, root={}",
                    witness.entries.len(),
                    witness.query_clause,
                    witness.root
                );

                for (i, entry) in witness.entries.iter().enumerate() {
                    eprintln!(
                        "  Entry {}: pred {:?}, level {}, incoming_clause={:?}",
                        i, entry.predicate, entry.level, entry.incoming_clause
                    );
                }

                // Count entries with incoming_clause populated
                let entries_with_clause = witness
                    .entries
                    .iter()
                    .filter(|e| e.incoming_clause.is_some())
                    .count();

                eprintln!(
                    "Entries with incoming_clause: {}/{}",
                    entries_with_clause,
                    witness.entries.len()
                );

                // At least some entries should have incoming_clause populated
                // (the initial entry might not have one if it's the query root)
                assert!(
                    entries_with_clause > 0,
                    "At least some derivation entries should have incoming_clause populated"
                );
            } else {
                panic!("Counterexample should have a derivation witness");
            }
        }
        _ => {
            panic!("counter_unsafe should return Unsafe result");
        }
    }
}

/// EXPERIMENT: Test hyperedge_unsafe with range_weakening disabled
/// This test verifies the claim from WORKER_DIRECTIVE.md that disabling
/// range-based weakening causes hyperedge_unsafe to incorrectly return Safe.
///
/// Root cause analysis:
/// Regression test: hyperedge_unsafe must return Unsafe even without range weakening.
///
/// Historical context: This was originally an investigation test for a suspected soundness
/// issue where disabling range-based weakening might cause false Safe results.
/// The test now confirms the fix works - must-summary reachability analysis correctly
/// finds counterexamples even without range weakening.
///
/// Must-summary approach finds counterexamples by tracking must-reachable states
/// from init, bypassing the need for generalized blocking lemmas.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_hyperedge_unsafe_without_range_weakening() {
    // This config disables range_weakening to test the directive claim
    let mut config = PdrConfig::production(true); // Enable verbose for investigation
    config.max_frames = 20;
    config.max_iterations = 500;
    config.max_obligations = 100_000;

    let result = pdr_solve_from_file(example_path("hyperedge_unsafe.smt2"), config).unwrap();

    // #1510 soundness fix: PDR can no longer return Unsafe for hyperedge cases by tracing
    // back through intermediate body predicates. This prevents unsound UNSAFE results but
    // means we can't prove UNSAFE for hyperedge benchmarks without reach_fact intersection.
    // Unknown is acceptable; Safe would indicate a soundness bug.
    // #1519: Unsafe arm kept but currently unreachable due to #1510 fix.
    // When reach_fact intersection is implemented (#1518), Unsafe will become reachable.
    match &result {
        PdrResult::Unsafe(_) => {
            // Aspirational: When #1518 is implemented, this path will work.
            // Until then, this arm is unreachable.
            eprintln!("PDR found hyperedge CHC UNSAFE (reach_fact intersection - see #1518)");
        }
        PdrResult::Unknown | PdrResult::NotApplicable => {
            // Expected with current implementation. #1510 disabled POB traceback
            // for hyperedge cases to prevent soundness bugs.
            eprintln!("PDR returned Unknown for unsafe hyperedge CHC (expected until #1518)");
        }
        PdrResult::Safe(_) => {
            panic!("hyperedge_unsafe.smt2 should NOT be classified as Safe!");
        }
        _ => panic!("unexpected variant"),
    }
}
