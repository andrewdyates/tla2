// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Part of #3355: deadlock detection in simulation mode

use super::*;

/// When check_deadlock is true (default), simulation must return Deadlock on
/// the first trace that reaches a state with no enabled actions.
/// Matches TLC SimulationWorker.java:692-696.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_deadlock_detected_when_check_deadlock_true() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter that deadlocks at x=5: Init starts at 0, Next increments while x < 5.
    let src = r#"
---- MODULE SimDeadlockDetect ----
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
        check_deadlock: true, // Explicitly enabled
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 10,
        max_trace_length: 100,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Deadlock { trace, stats } => {
            // First trace should deadlock, stopping simulation immediately
            assert_eq!(stats.traces_generated, 1);
            // Trace should be 0 -> 1 -> 2 -> 3 -> 4 -> 5 (6 states)
            assert_eq!(trace.states.len(), 6);
            let last_state = trace.states.last().unwrap();
            let x_val = last_state.get("x").unwrap();
            assert_eq!(*x_val, Value::int(5), "Deadlock should occur at x=5");
        }
        other => panic!("Expected Deadlock, got {:?}", other),
    }
}

/// When check_deadlock is false, deadlocked traces are counted silently
/// and simulation continues (no error).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_deadlock_silent_when_check_deadlock_false() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimDeadlockSilent ----
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
        check_deadlock: false,
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 5,
        max_trace_length: 100,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 5);
            assert_eq!(stats.deadlocked_traces, 5);
        }
        other => panic!(
            "Expected Success (deadlock check disabled), got {:?}",
            other
        ),
    }
}

/// Deadlock detection via the split-action path (use_split_actions = true).
/// Requires 2+ disjuncts so detect_simulation_actions finds multiple action
/// instances. Both actions deadlock at x=5 — covers the split-action gate at
/// simulation.rs:~501 (vs the fallback gate tested above).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_deadlock_split_action_path() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Two disjuncts: both become disabled when x >= 5
    let src = r#"
---- MODULE SimDeadlockSplitAction ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
A == x < 5 /\ x' = x + 1
B == x < 5 /\ x' = x + 2
Next == A \/ B
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: true,
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 10,
        max_trace_length: 100,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Deadlock { trace, stats } => {
            // First trace should deadlock at x=5 or x=6 depending on path
            assert_eq!(stats.traces_generated, 1);
            let last_state = trace.states.last().unwrap();
            let x_val = last_state.get("x").unwrap().as_i64().unwrap();
            assert!(
                x_val >= 5,
                "Deadlock should occur at x >= 5, got x={}",
                x_val
            );
        }
        other => panic!("Expected Deadlock (split-action path), got {:?}", other),
    }
}
