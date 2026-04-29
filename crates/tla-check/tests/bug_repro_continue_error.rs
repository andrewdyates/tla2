// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Continue-on-error TLC parity - Bug #595
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{CheckResult, Config, ModelChecker};

// ============================================================================
// Bug #595: Sequential checker --continue-on-error TLC parity
// ============================================================================

/// Bug #595: Sequential checker --continue-on-error must match TLC -continue
///
/// TLC -continue explores ALL reachable states, including successors of violating
/// states. Before the fix, TLA2 would count violating states but NOT explore their
/// successors, causing undercount.
///
/// Test spec: x increments 0->1->2->3->4->5, invariant x < 3 fails at x=3.
/// - Without continue: 4 states (0, 1, 2, 3-violated)
/// - With TLC -continue: 6 states (0, 1, 2, 3, 4, 5) - successors explored
///
/// TLC baseline: `java -jar ~/tlaplus/tla2tools.jar -workers 1 -continue`
///               reports `12 states generated, 6 distinct states found`
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_595_continue_on_error_tlc_parity() {
    let spec = r#"
---- MODULE ContinueOnErrorParity ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = x + 1 /\ x < 5

Spec == Init /\ [][Next]_x

SafeInvariant == x < 3

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafeInvariant".to_string()],
        ..Default::default()
    };

    // Run with continue_on_error to match TLC -continue semantics
    // Disable deadlock check since we're only testing state count parity
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_continue_on_error(true);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::InvariantViolation { stats, .. } => {
            // TLC -continue: 6 distinct states found
            // TLA2 --continue-on-error: must also find 6 states
            assert_eq!(
                stats.states_found, 6,
                "Bug #595: continue_on_error should find 6 states (TLC parity), got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #595: Expected InvariantViolation with 6 states, got: {:?}",
                other
            );
        }
    }
}

/// Bug #595: Verify continue_on_error disabled finds fewer states
///
/// Sanity check that without continue_on_error, we stop at the first violation
/// and find fewer states than TLC -continue mode.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_595_without_continue_on_error() {
    let spec = r#"
---- MODULE ContinueOnErrorDisabled ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = x + 1 /\ x < 5

SafeInvariant == x < 3

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafeInvariant".to_string()],
        ..Default::default()
    };

    // Run WITHOUT continue_on_error (default behavior)
    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.check();

    match &result {
        CheckResult::InvariantViolation { stats, .. } => {
            // BFS: 0,1,2,3 (x<3 violated at 3). Exactly 4 states.
            assert_eq!(
                stats.states_found, 4,
                "Without continue_on_error should find exactly 4 states (0,1,2,3), got {}",
                stats.states_found
            );
        }
        other => {
            panic!("Expected invariant violation, got: {:?}", other);
        }
    }
}

// Bug #595: Initial state invariant violation with continue_on_error
//
// Verifies that if an initial state violates an invariant, continue_on_error
// still explores successors from that state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_595_initial_state_violation_continue_on_error() {
    let spec = r#"
---- MODULE InitialViolationContinue ----
EXTENDS Naturals

VARIABLE x

\* Initial state violates invariant
Init == x = 5

Next == x' = x - 1 /\ x > 0

\* Invariant: x < 5 (violated by initial state)
SafeInvariant == x < 5

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafeInvariant".to_string()],
        ..Default::default()
    };

    // Run with continue_on_error
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_continue_on_error(true);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::InvariantViolation { stats, .. } => {
            // States: 5 (violated), 4, 3, 2, 1, 0 = 6 states
            // Even though initial state violates, we should explore successors
            assert_eq!(
                stats.states_found, 6,
                "Bug #595: initial violation continue_on_error should find 6 states, got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #595: Expected InvariantViolation from initial state, got: {:?}",
                other
            );
        }
    }
}

// Bug #595: Parallel checker initial state invariant violation with continue_on_error
//
// Verifies that if an initial state violates an invariant, the parallel checker still explores
// successors from that state in continue_on_error mode (matching TLC `-continue`).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bug_595_parallel_initial_state_violation_continue_on_error() {
    let spec = r#"
---- MODULE InitialViolationContinueParallel ----
EXTENDS Naturals

VARIABLE x

\* Initial state violates invariant
Init == x = 5

Next == x' = x - 1 /\ x > 0

\* Invariant: x < 5 (violated by initial state)
SafeInvariant == x < 5

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafeInvariant".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ParallelChecker::new(&module, &config, 2);
    checker.set_continue_on_error(true);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::InvariantViolation { stats, .. } => {
            assert_eq!(
                stats.states_found, 6,
                "Bug #595: parallel initial violation continue_on_error should find 6 states, got {} (stats={stats:?})",
                stats.states_found,
            );
        }
        other => {
            panic!(
                "Bug #595: Expected InvariantViolation from initial state (parallel), got: {:?}",
                other
            );
        }
    }
}

// Bug #595: Parallel checker --continue-on-error TLC parity
//
// Same as sequential test but verifies the parallel checker also handles
// continue_on_error correctly. The fix in commit fe18942f updated both
// check.rs (sequential) and parallel.rs (parallel) - both must be tested.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bug_595_parallel_continue_on_error_tlc_parity() {
    let spec = r#"
---- MODULE ContinueOnErrorParallelParity ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = x + 1 /\ x < 5

Spec == Init /\ [][Next]_x

SafeInvariant == x < 3

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafeInvariant".to_string()],
        ..Default::default()
    };

    // Run with parallel checker (2 workers) and continue_on_error
    let mut checker = tla_check::ParallelChecker::new(&module, &config, 2);
    checker.set_continue_on_error(true);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::InvariantViolation { stats, .. } => {
            // TLC -continue: 6 distinct states found
            // TLA2 parallel --continue-on-error: must also find 6 states
            assert_eq!(
                stats.states_found, 6,
                "Bug #595: parallel continue_on_error should find 6 states (TLC parity), got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #595: Expected InvariantViolation with 6 states from parallel checker, got: {:?}",
                other
            );
        }
    }
}
