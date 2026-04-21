// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Verify ACTION_CONSTRAINT filtering in simulation mode.
/// Uses a single-action Next (non-decomposable) so the full-state path evaluates
/// all successors and filters through constraints. Both x'=100 and x'=200
/// violate OnlySmallStep (x' < 10), so the trace should deadlock immediately.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_action_constraint_filters_successors() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimActionConstraintTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x = 0 /\ x' \in {100, 200}
OnlySmallStep == x' < 10
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["OnlySmallStep".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 1,
        max_trace_length: 5,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 1);
            assert_eq!(stats.deadlocked_traces, 1);
            assert_eq!(stats.transitions, 0);
            assert_eq!(
                stats.max_trace_length, 0,
                "ACTION_CONSTRAINT should reject all successors"
            );
        }
        other => panic!(
            "Expected Success with a deadlocked trace after ACTION_CONSTRAINT filtering, got {:?}",
            other
        ),
    }
}

/// Verify ACTION_CONSTRAINT allows valid successors while filtering invalid ones.
/// x' = x + 1 satisfies OnlySmallStep (x' < 10 when x < 9), so the trace
/// should make progress until x reaches 9.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_action_constraint_allows_valid_steps() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimActionConstraintAllowTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
OnlySmallStep == x' < 10
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["OnlySmallStep".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 1,
        max_trace_length: 20,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 1);
            // x goes 0→1→...→9, then x'=10 is rejected by constraint → deadlock
            assert_eq!(stats.deadlocked_traces, 1);
            assert_eq!(
                stats.transitions, 9,
                "Should allow 9 steps (x=0..8 → x'=1..9) before constraint blocks x'=10"
            );
        }
        other => panic!("Expected Success with 9 valid transitions, got {:?}", other),
    }
}
