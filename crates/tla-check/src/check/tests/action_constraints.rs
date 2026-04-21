// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================
// Action constraint tests
// ============================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_constraint_filters_transitions() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter that can go up or down
    // Action constraint only allows increasing transitions
    let src = r#"
---- MODULE ActionConstraintTest ----
EXTENDS Integers
VARIABLE x

Init == x = 0

\* Can increase by 1 or decrease by 1
Next == x' \in {x - 1, x + 1} /\ x < 5

\* Without constraint: x can go -1, 0, 1, -1, 0, 1, ... (bounded by x < 5)
\* With OnlyIncrease: x can only go 0, 1, 2, 3, 4, 5 (all positive, then deadlock)

\* Only allow increasing transitions
OnlyIncrease == x' > x
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // With action constraint: should only see non-negative states
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["OnlyIncrease".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // With OnlyIncrease constraint, we should see states 0, 1, 2, 3, 4, 5
            // The spec bounds x < 5 so Next is disabled at x=5
            assert_eq!(stats.states_found, 6, "Should find exactly 6 states: 0-5");
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

/// Negative control for test_action_constraint_filters_transitions:
/// the same spec WITHOUT the action constraint should produce more states.
/// Without this, a bug that unconditionally produces exactly 6 states
/// would pass the positive test.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_constraint_control_without_constraint() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Same spec but with a lower bound to keep the state space finite
    let src = r#"
---- MODULE ActionConstraintControlTest ----
EXTENDS Integers
VARIABLE x

Init == x = 0

\* Can increase by 1 or decrease by 1, bounded both ways
Next == x' \in {x - 1, x + 1} /\ x > -3 /\ x < 5

OnlyIncrease == x' > x
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Without action constraint: should find more states (negative values reachable)
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec![], // no constraint
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Without the constraint, x can go negative (0 -> -1 -> -2 -> -3)
            // bounded by x > -3 /\ x < 5, giving states {-3, -2, ..., 5} = 9 states
            // The key assertion: more than 6 states (which the constrained version finds)
            assert!(
                stats.states_found > 6,
                "Without constraint, should find more than 6 states (got {})",
                stats.states_found
            );
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_constraint_primed_and_unprimed() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test that action constraints can reference both x (current) and x' (next)
    let src = r#"
---- MODULE ActionConstraintPrimeTest ----
EXTENDS Integers
VARIABLE x

Init == x = 0

\* Can change by any amount from -2 to +2, bounded by range
Next == x' \in {x - 2, x - 1, x, x + 1, x + 2} /\ x >= -2 /\ x <= 2

\* Action constraint: only allow changes of exactly 1 in either direction (or stutter)
\* Uses both x (current) and x' (next)
SmallStep == x' = x + 1 \/ x' = x - 1 \/ x' = x
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["SmallStep".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // With SmallStep constraint and bounded Next, we can reach -3 to +3
            // States: -3, -2, -1, 0, 1, 2, 3 = 7 states
            assert_eq!(
                stats.states_found, 7,
                "Should find exactly 7 states: -3 to +3"
            );
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_constraint_empty() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Verify that empty action constraints list means no filtering
    let src = r#"
---- MODULE NoActionConstraintTest ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec![], // Empty
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4); // 0, 1, 2, 3
        }
        other => panic!("Expected Success, got {:?}", other),
    }
}
