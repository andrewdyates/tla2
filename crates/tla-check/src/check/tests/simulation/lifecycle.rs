// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Part of #3092: ASSUME / POSTCONDITION / TLCGet("config") coverage

use super::*;

/// ASSUME FALSE in simulation mode must return SimulationResult::Error with AssumeFalse.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_assume_false_returns_error() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimAssumeTest ----
EXTENDS Naturals
VARIABLE x
ASSUME FALSE
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
        num_traces: 10,
        max_trace_length: 10,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Error { error, .. } => {
            assert!(
                matches!(
                    error,
                    CheckError::Runtime(RuntimeCheckError::AssumeFalse { .. })
                ),
                "Expected AssumeFalse, got {:?}",
                error
            );
        }
        other => panic!(
            "Expected SimulationResult::Error(AssumeFalse), got {:?}",
            other
        ),
    }
}

/// POSTCONDITION == FALSE must return SimulationResult::Error with PostconditionFalse.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_postcondition_false_returns_error() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimPostcondTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
AlwaysFalse == FALSE
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("AlwaysFalse".to_string()),
        check_deadlock: false, // Allow deadlock so simulation reaches postcondition check
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
        SimulationResult::Error { error, .. } => {
            assert!(
                matches!(
                    error,
                    CheckError::Runtime(RuntimeCheckError::PostconditionFalse { .. })
                ),
                "Expected PostconditionFalse, got {:?}",
                error
            );
        }
        other => panic!(
            "Expected SimulationResult::Error(PostconditionFalse), got {:?}",
            other
        ),
    }
}

/// POSTCONDITION that checks TLCGet("stats").diameter must see the correct trace depth.
/// In simulation mode, diameter = max trace length across all traces.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_postcondition_diameter() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter that deadlocks at x=3 (trace length = 3 steps: 0→1→2→3).
    // POSTCONDITION checks that diameter > 0 (i.e., depth was propagated).
    let src = r#"
---- MODULE SimDiameterTest ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
DiameterPositive == TLCGet("stats").diameter > 0
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("DiameterPositive".to_string()),
        check_deadlock: false, // Allow deadlock without error (testing postcondition)
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 5,
        max_trace_length: 20,
        seed: Some(42),
        check_invariants: false,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    match result {
        SimulationResult::Success(stats) => {
            // All traces deadlock at x=3, so max_trace_length should be 3.
            assert_eq!(stats.max_trace_length, 3, "Expected max trace length 3");
            assert!(stats.traces_generated > 0);
        }
        other => panic!(
            "Expected Success (postcondition diameter>0 passes), got {:?}",
            other
        ),
    }
}

/// TLCGet("config").traces and TLCGet("config").seed must reflect simulation config.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simulation_tlcget_config_traces_and_seed() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // The invariant checks that TLCGet("config").traces = 7 and
    // TLCGet("config").seed = 999 during simulation. If the values aren't
    // propagated, the Assert will fail.
    let src = r#"
---- MODULE SimTLCGetConfigTest ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
ConfigCheck == Assert(
    TLCGet("config").traces = 7 /\ TLCGet("config").seed = 999,
    "TLCGet config mismatch")
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["ConfigCheck".to_string()],
        check_deadlock: false, // Allow deadlock without error (testing TLCGet config)
        ..Default::default()
    };

    let sim_config = SimulationConfig {
        num_traces: 7,
        max_trace_length: 10,
        seed: Some(999),
        check_invariants: true,
        action_constraints: Vec::new(),
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.simulate(&sim_config);

    // If TLCGet("config") values were correctly propagated, the Assert invariant passes
    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 7);
        }
        SimulationResult::InvariantViolation { invariant, .. } => {
            panic!(
                "TLCGet config values not propagated: invariant {} failed",
                invariant
            );
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}
