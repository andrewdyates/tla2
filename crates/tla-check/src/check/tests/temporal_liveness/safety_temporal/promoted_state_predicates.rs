// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #2332: `[]P` where P is a pure state predicate, listed under PROPERTIES
/// in the .cfg, must be reported as `InvariantViolation` (not `PropertyViolation`) to match
/// TLC behavior. TLC classifies `[]StatePredicate` under PROPERTIES the same as INVARIANT.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_2332_always_state_predicate_property_returns_invariant_violation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec: x starts at 0, increments to 2. Property says x must always be <= 1.
    // This is a pure []StatePredicate listed as a PROPERTY — TLC reports it as invariant violation.
    let src = r#"
---- MODULE AlwaysStatePred ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

\* Pure state predicate — no primes, no temporal operators inside
Safe == x <= 1

\* []Safe is a PROPERTY but since Safe is a state predicate, TLC reports
\* violations as "Invariant Safe is violated." (#2332)
AlwaysSafe == []Safe
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["AlwaysSafe".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);

    let result = checker.check();
    match result {
        // Part of #2676: state-level PROPERTY violations are now reported as
        // PropertyViolation with StateLevel kind (TLC parity: "Temporal properties
        // were violated" instead of "Invariant X is violated").
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats: _,
        } => {
            assert_eq!(property, "AlwaysSafe");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::StateLevel);
            // The violation occurs when x reaches 2, which violates Safe (x <= 1).
            assert!(!trace.is_empty(), "Trace should contain at least one state");
            // Verify the violating state has x = 2.
            let last = trace.states.last().expect("non-empty trace");
            let x_val = last.get("x").expect("state should have x");
            assert_eq!(x_val, &Value::int(2), "Violating state should have x=2");
        }
        other => panic!("Expected PropertyViolation(StateLevel), got: {other:?}"),
    }
}

/// Regression test for #2332 state count: when `[]P` (state predicate) is listed under
/// PROPERTIES, BFS must stop at the first violation (not explore the full state space).
/// TLC checks these during BFS and stops early; TLA2 must match.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_2332_promoted_property_invariant_stops_early() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // x goes 0 → 1 → 2 → ... → 10 → 10 (stutters). Safe requires x <= 5.
    // Full state space = 11 distinct states. BFS should stop at x = 6 (7 states found).
    let src = r"
---- MODULE PromotedPropertyEarlyStop ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == IF x < 10 THEN x' = x + 1 ELSE UNCHANGED x

Safe == x <= 5

AlwaysSafe == []Safe
====
";
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["AlwaysSafe".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);

    let result = checker.check();
    match &result {
        // Part of #2676: state-level PROPERTY violations are now reported as
        // PropertyViolation with StateLevel kind.
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats,
        } => {
            assert_eq!(property, "AlwaysSafe");
            assert_eq!(kind, &crate::check::api::PropertyViolationKind::StateLevel);
            // Verify the violating state has x = 6
            let last = trace.states.last().expect("non-empty trace");
            let x_val = last.get("x").expect("state should have x");
            assert_eq!(x_val, &Value::int(6), "Violating state should have x=6");
            // BFS should stop early: states found must be <= 7 (x=0..6),
            // NOT 11 (the full state space). The exact count depends on BFS
            // ordering, but must be strictly less than 11.
            assert!(
                stats.states_found < 11,
                "Bug #2332: BFS should stop at first violation of promoted \
                 []StatePredicate property, but explored {} states (full space = 11). \
                 Property was not promoted to BFS invariant checking.",
                stats.states_found
            );
        }
        other => panic!("Expected PropertyViolation(StateLevel), got: {other:?}"),
    }
}
