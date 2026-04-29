// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_basic() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Simple counter that goes 0 -> 1 -> 2 -> 3 -> 4 -> 5 (deadlock)
    let src = r#"
---- MODULE SimTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false, // Allow deadlock without error (testing trace stats)
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 10,
        max_trace_length: 100,
        seed: Some(42),
        check_invariants: true,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 10);
            // All traces should deadlock at x=5
            assert_eq!(stats.deadlocked_traces, 10);
            assert_eq!(stats.truncated_traces, 0);
            // Should find all 6 distinct states (0..5)
            assert_eq!(stats.distinct_states, 6);
            // Max trace length is 5 (0 -> 1 -> 2 -> 3 -> 4 -> 5)
            assert_eq!(stats.max_trace_length, 5);
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_reproducible_with_seed() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Branching spec with multiple choices at each step
    let src = r#"
---- MODULE SimSeedTest ----
EXTENDS Naturals
VARIABLE x
Init == x \in {1, 2, 3}
Next == x' \in {x + 1, x + 2, x + 3}
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    // Run twice with same seed
    let sim_config = SimulationConfig {
        num_traces: 10,
        max_trace_length: 5,
        seed: Some(12345),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker1 = ModelChecker::new(&module, &config);
    let result1 = checker1.simulate(&sim_config);

    let mut checker2 = ModelChecker::new(&module, &config);
    let result2 = checker2.simulate(&sim_config);

    // Results should be identical
    match (result1, result2) {
        (SimulationResult::Success(stats1), SimulationResult::Success(stats2)) => {
            assert_eq!(stats1.traces_generated, stats2.traces_generated);
            assert_eq!(stats1.states_visited, stats2.states_visited);
            assert_eq!(stats1.distinct_states, stats2.distinct_states);
            assert_eq!(stats1.transitions, stats2.transitions);
        }
        (r1, r2) => panic!("Expected both to succeed, got {:?} and {:?}", r1, r2),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_max_trace_length() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Infinite spec (can always increment)
    let src = r#"
---- MODULE SimMaxLenTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 5,
        max_trace_length: 10,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 5);
            // All traces should hit the max length limit
            assert_eq!(stats.truncated_traces, 5);
            assert_eq!(stats.deadlocked_traces, 0);
            assert_eq!(stats.max_trace_length, 10);
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_no_invariant_checking() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Same spec as invariant violation test, but with invariant checking disabled
    let src = r#"
---- MODULE SimNoInvTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
BadInvariant == x <= 2
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["BadInvariant".to_string()],
        check_deadlock: false, // Allow deadlock without error
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 10,
        max_trace_length: 100,
        seed: Some(42),
        check_invariants: false, // Disabled!
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    // Should succeed because we're not checking invariants
    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 10);
        }
        other => panic!("Expected Success (no invariant check), got {:?}", other),
    }
}
