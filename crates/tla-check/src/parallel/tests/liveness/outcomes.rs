// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core liveness outcomes and parity tests.

use super::*;

/// Part of #2740: Parallel checker now supports liveness properties.
/// `<>TRUE` is a tautology — the negation `[]FALSE` is trivially unsatisfiable,
/// so the checker reports `LiveFormulaTautology` (matching sequential/TLC behavior).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_liveness_tautology_detected() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelLivenessTautology ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == <>TRUE
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    match result {
        CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::FormulaTautology { property }),
            ..
        } => {
            assert_eq!(property, "Prop");
        }
        other => panic!("Expected LiveFormulaTautology for <>TRUE property, got: {other:?}"),
    }
}

/// Part of #2740: Verify that the parallel checker DETECTS liveness violations.
/// This spec has x stuck at 0 (UNCHANGED x), so `<>(x = 1)` is violated.
/// Both parallel and sequential checkers must report a liveness violation.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_liveness_violation_detected() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelLivenessViolation ----
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Prop == <>(x = 1)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    match result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(property, "Prop", "Expected violation of property 'Prop'");
        }
        other => {
            panic!("Expected LivenessViolation for <>(x = 1) with UNCHANGED x, got: {other:?}")
        }
    }
}

/// Part of #2740: Verify that the parallel checker reports success when a
/// liveness property IS satisfied. Since `Init == x = 0` and `Next == UNCHANGED x`,
/// x is always 0 in every reachable state, so `<>(x = 0)` is trivially satisfied
/// (the init state already satisfies it, and there are no behaviors where x != 0).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_liveness_satisfied() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelLivenessSatisfied ----
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Prop == <>(x = 0)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Expected 1 state (x=0)");
        }
        other => panic!("Expected Success for <>(x = 0) with Init x=0, got: {other:?}"),
    }
}

/// Parity test: mixed safety+liveness property with tautological liveness part.
///
/// The property `[]TypeOK /\ <>TRUE` has a safety part (`[]TypeOK`) and a
/// tautological liveness part (`<>TRUE`). The sequential checker separates
/// safety from liveness via `separate_safety_liveness_parts()` before tautology
/// checking, so it detects `<>TRUE` as tautological and rejects pre-BFS.
///
/// The parallel checker's `check_property_tautologies()` in `checker_ops.rs`
/// now also pre-separates safety/liveness conjuncts via `is_liveness_conjunct()`
/// and only checks the liveness terms for tautology, matching sequential behavior.
/// Previously (before P1-894 fix), it converted the ENTIRE property body without
/// pre-separation, causing mixed tautologies to go undetected.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_mixed_safety_liveness_tautology_detected() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelMixedTautology ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
TypeOK == x \in 0..2
Prop == []TypeOK /\ <>TRUE
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    // Both sequential and parallel checkers detect this as tautological by
    // pre-separating safety ([]TypeOK) from liveness (<>TRUE) and checking
    // the liveness portion independently for tautology.
    match result {
        CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::FormulaTautology { property }),
            ..
        } => {
            assert_eq!(property, "Prop");
        }
        other => panic!(
            "Expected LiveFormulaTautology for []TypeOK /\\ <>TRUE mixed property, \
             got: {other:?}. This indicates the parallel checker's pre-BFS tautology \
             check does not pre-separate safety/liveness parts."
        ),
    }
}

/// Mirror test: verify sequential checker catches mixed safety+liveness tautology.
/// This confirms the expected behavior that the parallel test above should match.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_mixed_safety_liveness_tautology_detected() {
    let _serial = super::super::acquire_interner_lock();
    use crate::check::model_checker::ModelChecker;

    let src = r"
---- MODULE SequentialMixedTautology ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
TypeOK == x \in 0..2
Prop == []TypeOK /\ <>TRUE
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::FormulaTautology { property }),
            ..
        } => {
            assert_eq!(property, "Prop");
        }
        other => panic!("Expected LiveFormulaTautology for []TypeOK /\\ <>TRUE, got: {other:?}"),
    }
}

/// Part of #2752: Sequential/parallel parity test for liveness.
///
/// Runs both the sequential `ModelChecker` and parallel `ParallelChecker` on
/// the same spec with a liveness violation and verifies:
/// 1. Both report a `LivenessViolation` (identical classification)
/// 2. Both report the same property name
/// 3. Both report the same state count
///
/// This satisfies acceptance criterion 5: "At least one liveness spec matches
/// sequential/TLC classification and state count under parallel mode."
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_liveness_parity() {
    let _serial = super::super::acquire_interner_lock();
    use crate::check::model_checker::ModelChecker;

    let src = r"
---- MODULE LivenessParity ----
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Prop == <>(x = 1)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    // Sequential checker
    let mut seq_checker = ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    // Part of #3175: set_store_states initializes cache_for_liveness from config.
    // Without this call, cache_for_liveness defaults to false and liveness is skipped.
    seq_checker.set_store_states(false);
    let seq_result = seq_checker.check();

    // Parallel checker
    let checker = ParallelChecker::new(&module, &config, 2);
    let par_result = checker.check();

    // Both must be LivenessViolation
    let (seq_prop, seq_states) = match &seq_result {
        CheckResult::LivenessViolation {
            property, stats, ..
        } => (property.clone(), stats.states_found),
        other => panic!("Sequential: expected LivenessViolation, got: {other:?}"),
    };

    let (par_prop, par_states) = match &par_result {
        CheckResult::LivenessViolation {
            property, stats, ..
        } => (property.clone(), stats.states_found),
        other => panic!("Parallel: expected LivenessViolation, got: {other:?}"),
    };

    assert_eq!(
        seq_prop, par_prop,
        "Property name mismatch: sequential={seq_prop}, parallel={par_prop}"
    );
    assert_eq!(
        seq_states, par_states,
        "State count mismatch: sequential={seq_states}, parallel={par_states}"
    );
}
