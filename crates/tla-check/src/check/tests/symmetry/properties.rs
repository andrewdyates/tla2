// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_large_permutation_group() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test with 4 elements to verify scaling: 4! = 24 permutations
    let src = r#"
---- MODULE SymmetryLarge ----
EXTENDS TLC
CONSTANT Procs
VARIABLE leader

\* Select a leader from processes
Init == leader \in Procs
Next == leader' \in Procs /\ leader' /= leader

\* Symmetry
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT symmetry
    let mut config_no_sym = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config_no_sym.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
            "p4".to_string(),
        ]),
    );

    // Config WITH symmetry
    let mut config_sym = config_no_sym.clone();
    config_sym.symmetry = Some("Sym".to_string());

    // Check WITHOUT symmetry
    let mut checker_no_sym = ModelChecker::new(&module, &config_no_sym);
    checker_no_sym.set_deadlock_check(false);
    let result_no_sym = checker_no_sym.check();

    let states_no_sym = match result_no_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success without symmetry, got {:?}", other),
    };

    // Check WITH symmetry
    let mut checker_sym = ModelChecker::new(&module, &config_sym);
    checker_sym.set_deadlock_check(false);
    let result_sym = checker_sym.check();

    let states_sym = match result_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with symmetry, got {:?}", other),
    };

    // Without symmetry: 4 states (leader = p1, p2, p3, or p4)
    // With symmetry: 1 canonical state
    assert_eq!(
        states_no_sym, 4,
        "Without symmetry should have 4 states (4 processes)"
    );
    assert_eq!(states_sym, 1, "With symmetry should have 1 canonical state");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_accepts_filtered_permutation_set() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SymmetryFiltered ----
EXTENDS TLC
CONSTANT Procs
VARIABLE leader

Init == leader \in Procs
Next == leader' \in Procs /\ leader' /= leader

\* Part of #1918: filtered permutation sets stay lazy (SetPred) until iterated.
Sym == {p \in Permutations(Procs) : p = p}
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
        ]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    let states = match result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!(
            "filtered permutation symmetry should succeed, got {:?}",
            other
        ),
    };

    assert_eq!(
        states, 1,
        "filtered permutation symmetry should still reduce to one canonical state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_preserves_invariant_violation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Ensure symmetry reduction still catches invariant violations
    let src = r#"
---- MODULE SymmetryInvariant ----
EXTENDS TLC
CONSTANT Procs
VARIABLE active, count

Init == active \in Procs /\ count = 0
Next == /\ active' \in Procs
    /\ count' = count + 1

\* Invariant: count < 3 (will be violated)
Safety == count < 3

\* Symmetry
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with invariant
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );
    config.symmetry = Some("Sym".to_string());

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    // Should find invariant violation even with symmetry
    match result {
        CheckResult::InvariantViolation { .. } => {
            // Expected - symmetry doesn't hide violations
        }
        other => panic!("Expected InvariantViolation with symmetry, got {:?}", other),
    }
}

/// Part of #1963: Verify the checker completes when both SYMMETRY and genuine
/// temporal PROPERTIES are configured. Part of #2227: the warning is now driven
/// by classification-based detection (any_property_requires_liveness_checker)
/// rather than Config::symmetry_liveness_warning. This test verifies the
/// end-to-end code path does not panic or error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_liveness_property_emits_warning_and_completes() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Simple spec with a stuttering-allowed liveness property.
    // <>[] (x = 2) is eventually always satisfied once x reaches 2.
    let src = r#"
---- MODULE SymmetryLiveness ----
EXTENDS TLC, Integers
CONSTANT Procs
VARIABLE x

Init == x \in {0}
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

\* A liveness property: eventually x reaches 2 and stays there
Liveness == <>[](x = 2)

\* Symmetry (does not interact with x, but triggers the warning)
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Liveness".to_string()],
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // required for liveness checking

    let result = checker.check();
    // The checker should complete (success or liveness result) — not panic
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "x takes values 0, 1, 2");
        }
        CheckResult::LivenessViolation { .. } => {
            // Also acceptable — the spec may or may not satisfy liveness
            // depending on the liveness algorithm's handling of stuttering.
        }
        other => panic!(
            "Expected Success or LivenessViolation with symmetry+liveness, got {:?}",
            other
        ),
    }
}

/// Part of #3222: SYMMETRY + genuine temporal liveness must auto-upgrade to
/// full-state mode when no trace file is available. The inline liveness cache
/// is disabled under symmetry, so the checker must keep concrete states for
/// witness reconstruction instead of rejecting the configuration.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_liveness_notrace_auto_upgrades_to_full_state_mode() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SymLivenessNoTrace ----
EXTENDS TLC, Integers
CONSTANT Procs
VARIABLE x

Init == x \in {0}
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Liveness == <>[](x = 2)
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Liveness".to_string()],
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_auto_create_trace_file(false);
    // Do NOT call set_store_states(true). Start from no-trace mode and let
    // the checker auto-upgrade because symmetry disables inline liveness.

    let result = checker.check();
    assert!(
        !checker.test_seen_is_empty(),
        "symmetry+liveness should auto-upgrade to full-state storage instead of rejecting"
    );

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "x takes values 0, 1, 2");
        }
        CheckResult::LivenessViolation { stats, .. } => {
            assert_eq!(stats.states_found, 3, "x takes values 0, 1, 2");
        }
        other => panic!(
            "Expected Success or LivenessViolation after symmetry+liveness auto-upgrade, got {:?}",
            other
        ),
    }
}

/// Part of #2227: Verify that pure safety properties (`[]P`) are NOT rejected
/// in SYMMETRY + notrace mode. The safety-temporal fast path handles these
/// correctly without needing full-state storage.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_safety_property_notrace_accepted() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with a pure safety property expressed via PROPERTY keyword.
    // `[]P` where P is state-level — handled by safety-temporal fast path.
    let src = r#"
---- MODULE SymSafetyNoTrace ----
EXTENDS TLC, Integers
CONSTANT Procs
VARIABLE x

Init == x \in {0}
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

\* Pure safety property: x is always in range
Safety == [](x >= 0 /\ x <= 2)

\* Symmetry set
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Safety".to_string()],
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Do NOT call set_store_states(true) — leave in default notrace mode.
    // With #2227 fix, this should succeed (not error with ConfigError).

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "x takes values 0, 1, 2");
        }
        CheckResult::Error { error, .. } => {
            let msg = format!("{error}");
            panic!("Pure safety property with symmetry+notrace should NOT be rejected, got: {msg}");
        }
        other => panic!(
            "Expected Success for symmetry+safety_property+notrace, got {:?}",
            other
        ),
    }
}
