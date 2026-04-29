// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;


// ============================
// End-to-end model checking tests
// ============================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_simple_counter() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // A counter that increments from 0 to 2 with a bounded constraint
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
InRange == x >= 0 /\ x <= 2
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    // Allow deadlock since x=2 has no successors (x < 2 is false)
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Should find 3 states: x=0, x=1, x=2
            assert_eq!(stats.states_found, 3);
            assert_eq!(stats.initial_states, 1);
            // Transitions: 0->1, 1->2 = 2 transitions
            assert_eq!(stats.transitions, 2);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_invariant_violation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter starts at 0, increments unboundedly
    // Invariant x < 3 should be violated when x reaches 3
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
SmallValue == x < 3
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SmallValue".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            assert_eq!(invariant, "SmallValue");
            // Trace should show path from x=0 to x=3
            assert_eq!(trace.len(), 4); // x=0, x=1, x=2, x=3
            assert_eq!(stats.states_found, 4); // Linear spec: exactly 4 states
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_invariant_eval_error_is_error_not_violation() {
    use crate::error::EvalError;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // TLC errors when attempting to enumerate a non-enumerable function set.
    let src = r#"
---- MODULE FuncSetEmptyEquality ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == [Nat -> Nat] = {}
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::SetTooLarge { .. })) => {}
            other => panic!("Expected SetTooLarge EvalError, got: {:?}", other),
        },
        other => panic!("Expected Error, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_multiple_initial_states() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Multiple initial states: x can be 0 or 1
    let src = r#"
---- MODULE Multi ----
VARIABLE x
Init == x \in {0, 1}
Next == x < 3 /\ x' = x + 1
InRange == x >= 0 /\ x <= 3
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Initial: x=0, x=1
            // From x=0: can reach x=1, x=2, x=3
            // From x=1: can reach x=2, x=3
            // Unique states: 0, 1, 2, 3 = 4 states
            assert_eq!(stats.initial_states, 2);
            assert_eq!(stats.states_found, 4);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_disjunctive_init() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Disjunctive Init: x starts as 0 or 1
    let src = r#"
---- MODULE DisjInit ----
VARIABLE x
Init == x = 0 \/ x = 1
Next == x < 3 /\ x' = x + 1
InRange == x >= 0 /\ x <= 3
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 2);
            assert_eq!(stats.states_found, 4); // x=0,1,2,3
            assert_eq!(stats.transitions, 3);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_two_variables() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Two variables: x increments, y stays the same
    let src = r#"
---- MODULE TwoVars ----
VARIABLE x, y
Init == x = 0 /\ y = 5
Next == x' = x + 1 /\ UNCHANGED y
Bounded == x < 2
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Bounded".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats: _,
        } => {
            assert_eq!(invariant, "Bounded");
            // BFS finds violation at x=2: trace is [x=0, x=1, x=2] exactly
            assert_eq!(trace.len(), 3);

            // Verify the violating (last) state has x=2 — the count-only check
            // above would pass even if the trace contained wrong states.
            let last = trace.states.last().unwrap();
            assert_eq!(
                last.get("x"),
                Some(&Value::int(2)),
                "violating state should have x=2"
            );

            // Verify y stayed unchanged in all states
            for state in &trace.states {
                let y_val = state.vars().find(|(n, _)| n.as_ref() == "y");
                assert!(y_val.is_some());
                assert_eq!(y_val.unwrap().1, &Value::int(5));
            }
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_disjunctive_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Next has disjunction: can increment by 1 or 2
    let src = r#"
---- MODULE Disjunction ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 \/ x' = x + 2
SmallValue == x < 4
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SmallValue".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats: _,
        } => {
            assert_eq!(invariant, "SmallValue");
            // BFS shortest path: x=0 -> x=2 -> x=4 (length 3)
            assert_eq!(trace.len(), 3);
            // Verify trace starts at x=0 and the violating state has x >= 4.
            assert_eq!(
                trace.states[0].get("x"),
                Some(&Value::int(0)),
                "trace should start at x=0"
            );
            let last_x = trace.states.last().unwrap().get("x").unwrap().clone();
            assert!(
                last_x >= Value::int(4),
                "violating state should have x >= 4, got {:?}",
                last_x
            );
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_in_set_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test x' \in S in Next relation - counter can jump by 1, 2, or 3
    let src = r#"
---- MODULE InSetCounter ----
VARIABLE x
Init == x = 0
Next == x' \in {x + 1, x + 2, x + 3}
SmallValue == x < 5
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SmallValue".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            assert_eq!(invariant, "SmallValue");
            // BFS shortest counterexample: x=0 -> x=2 -> x=5 (3 states)
            assert_eq!(trace.len(), 3);
            // Should have explored states 0,1,2,3,4 (at least 5)
            assert!(stats.states_found >= 5);
            // Verify trace starts at x=0 and the violating state has x >= 5
            // (SmallValue == x < 5).
            assert_eq!(
                trace.states[0].get("x"),
                Some(&Value::int(0)),
                "trace should start at x=0"
            );
            let last_x = trace.states.last().unwrap().get("x").unwrap().clone();
            assert!(
                last_x >= Value::int(5),
                "violating state should have x >= 5, got {:?}",
                last_x
            );
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_in_set_cartesian() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test x' \in S and y' \in T - cartesian product of transitions
    let src = r#"
---- MODULE Cartesian ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' \in {0, 1} /\ y' \in {0, 1}
Sum == x + y < 2
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Sum".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            assert_eq!(invariant, "Sum");
            // x=1, y=1 violates Sum (1+1 = 2, not < 2)
            // Total states: (0,0), (0,1), (1,0), (1,1) = 4 states
            assert_eq!(stats.states_found, 4); // Finite 4-state space
                                               // BFS: (0,0) -> (1,1) is one step, trace = [init, violating]
            assert_eq!(trace.len(), 2);
            // Verify the violating state has x + y >= 2 (Sum == x + y < 2).
            let last = trace.states.last().unwrap();
            let x_val = last.get("x").expect("violating state should have x");
            let y_val = last.get("y").expect("violating state should have y");
            assert_eq!(x_val, &Value::int(1), "violating state should have x=1");
            assert_eq!(y_val, &Value::int(1), "violating state should have y=1");
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}
