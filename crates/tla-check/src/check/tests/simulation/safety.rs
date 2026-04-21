// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_with_invariant_violation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter that goes 0 -> 1 -> 2 -> 3, but invariant says x <= 2
    let src = r#"
---- MODULE SimInvariantTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
SafetyInvariant == x <= 2
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafetyInvariant".to_string()],
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 100,
        max_trace_length: 100,
        seed: Some(42),
        check_invariants: true,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::InvariantViolation {
            invariant,
            trace,
            stats: _,
        } => {
            assert_eq!(invariant, "SafetyInvariant");
            // Trace should end at a state where x = 3 (violates x <= 2)
            let last_state = trace.states.last().unwrap();
            let x_val = last_state.get("x").unwrap();
            assert_eq!(*x_val, Value::int(3));
        }
        other => panic!("Expected InvariantViolation, got {:?}", other),
    }
}

// Part of #1117: TLCExt!Trace simulation mode test
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_tlcext_trace() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec that uses TLCExt!Trace in an invariant
    // The invariant checks that Trace length matches the expected depth (x + 1)
    let src = r#"
---- MODULE SimTraceTest ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
\* Trace should be a sequence of records, length = x + 1 at each state
TraceInvariant == Len(Trace) = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TraceInvariant".to_string()],
        check_deadlock: false, // Allow deadlock without error (testing Trace invariant)
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 10,
        max_trace_length: 10,
        seed: Some(42),
        check_invariants: true,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    // If Trace works correctly, invariant should pass
    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 10);
            // All traces should deadlock at x=5
            assert_eq!(stats.deadlocked_traces, 10);
        }
        SimulationResult::InvariantViolation {
            invariant, trace, ..
        } => {
            panic!(
                "TLCExt!Trace invariant failed: {} at state {:?}, trace length {}",
                invariant,
                trace.states.last(),
                trace.states.len()
            );
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_constraint_false_uses_trace_count_and_ends_trace_without_deadlock() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimConstraintTraceCount ----
EXTENDS TLC, Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Stop == x = 1 => Assert(
    TLCGet("diameter") = TLCGet("stats").traces /\
    TLCGet("stats").traces \in 1..3,
    "bad stats"
) /\ FALSE
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["Stop".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 3,
        max_trace_length: 10,
        seed: Some(1),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 3);
            // Part of #3083: constraint-filtered traces now count as deadlocked
            // in the fallback path, matching the split-action path's behavior.
            assert_eq!(stats.deadlocked_traces, 3);
            assert_eq!(stats.max_trace_length, 0);
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}
