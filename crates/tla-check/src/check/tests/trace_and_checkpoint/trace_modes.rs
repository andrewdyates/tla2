// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_trace_mode_success() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
TypeOK == x \in {0, 1, 2}
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Run with no-trace mode
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(false);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "Should find 3 states");
            // Verify internal state: seen_fps should be populated, seen should be empty
            assert!(
                checker.test_seen_is_empty(),
                "seen map should be empty in no-trace mode"
            );
            assert_eq!(
                checker.test_seen_fps_len(),
                3,
                "seen_fps should have 3 entries"
            );
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_trace_mode_violation_empty_trace() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
NeverTwo == x /= 2
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NeverTwo".to_string()],
        ..Default::default()
    };

    // Run with no-trace mode (disables both full-state storage AND auto trace file)
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(false);
    checker.set_auto_create_trace_file(false); // Required for truly empty traces
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant, trace, ..
        } => {
            assert_eq!(invariant, "NeverTwo");
            // In no-trace mode (with auto trace file disabled), trace should be empty
            assert!(trace.is_empty(), "Trace should be empty in no-trace mode");
        }
        other => panic!("Expected InvariantViolation, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_mode_vs_no_trace_mode_state_count() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == (x' = (x + 1) % 2) /\ (y' = (y + 1) % 2)
TypeOK == x \in {0, 1} /\ y \in {0, 1}
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Run with trace mode (default)
    let mut checker_trace = ModelChecker::new(&module, &config);
    checker_trace.set_deadlock_check(false);
    let result_trace = checker_trace.check();

    // Run with no-trace mode
    let mut checker_no_trace = ModelChecker::new(&module, &config);
    checker_no_trace.set_store_states(false);
    checker_no_trace.set_deadlock_check(false);
    let result_no_trace = checker_no_trace.check();

    // Both should find the same number of states
    let states_trace = match result_trace {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success (trace), got {:?}", other),
    };

    let states_no_trace = match result_no_trace {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success (no-trace), got {:?}", other),
    };

    assert_eq!(
        states_trace, states_no_trace,
        "Both modes should find same state count"
    );
    // With the given Next relation, (0,0) -> (1,1) -> (0,0)... only 2 reachable states
    assert_eq!(states_trace, 2, "Should find 2 states: (0,0), (1,1)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_view_reduces_state_space() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with two variables: x (main state) and counter (auxiliary)
    // Without VIEW: states distinguished by both x and counter
    // With VIEW: states only distinguished by x (counter ignored)
    let src = r#"
---- MODULE Test ----
VARIABLE x, counter
Init == x = 0 /\ counter = 0
Next == x' = (x + 1) % 3 /\ counter' = counter + 1
TypeOK == x \in {0, 1, 2}

\* VIEW expression: only consider x for fingerprinting
ViewX == x
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT VIEW
    let config_no_view = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Config WITH VIEW
    let mut config_with_view = config_no_view.clone();
    config_with_view.view = Some("ViewX".to_string());

    // Without VIEW: counter keeps incrementing, so we get many states
    // Actually, with counter growing unboundedly, we need a depth limit
    let mut checker_no_view = ModelChecker::new(&module, &config_no_view);
    checker_no_view.set_deadlock_check(false);
    checker_no_view.set_max_depth(5); // Limit depth to prevent infinite exploration
    let result_no_view = checker_no_view.check();

    let states_no_view = match result_no_view {
        CheckResult::Success(stats) => stats.states_found,
        CheckResult::LimitReached { stats, .. } => stats.states_found,
        other => panic!(
            "Expected Success or LimitReached without VIEW, got {:?}",
            other
        ),
    };

    // With VIEW: counter changes don't create new states (VIEW only looks at x)
    let mut checker_with_view = ModelChecker::new(&module, &config_with_view);
    checker_with_view.set_deadlock_check(false);
    checker_with_view.set_max_depth(5);
    let result_with_view = checker_with_view.check();

    let states_with_view = match result_with_view {
        CheckResult::Success(stats) => stats.states_found,
        CheckResult::LimitReached { stats, .. } => stats.states_found,
        other => panic!(
            "Expected Success or LimitReached with VIEW, got {:?}",
            other
        ),
    };

    // VIEW should reduce state count: only 3 distinct x values (0, 1, 2)
    assert_eq!(
        states_with_view, 3,
        "With VIEW, should only see 3 states (x values)"
    );

    // Without VIEW, we get more states (one per (x, counter) pair)
    // At depth 5, we get: initial + 5 successor states = 6 states
    assert!(
        states_no_view > states_with_view,
        "Without VIEW should have more states ({}) than with VIEW ({})",
        states_no_view,
        states_with_view
    );
}
