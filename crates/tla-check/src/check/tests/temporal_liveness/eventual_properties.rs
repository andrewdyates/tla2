// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_enabled_counts_stuttering_successors() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Regression test: ENABLED(A) must consider stuttering successors (s -> s).
    // In particular, ENABLED(UNCHANGED x) should be TRUE, since UNCHANGED x is always enabled.
    let src = r#"
---- MODULE EnabledStutter ----
VARIABLE x
vars == <<x>>

Init == x = 0

Stutter == UNCHANGED x
Next == Stutter

EnabledStutter == ENABLED Stutter
Prop == []EnabledStutter
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Verify the checker actually explored the state space.
            // A checker that silently returns Success without running would pass
            // a bare `matches!(result, CheckResult::Success(_))` assertion.
            assert_eq!(
                stats.states_found, 1,
                "expected 1 state (x=0 with only UNCHANGED x transitions), got {}",
                stats.states_found
            );
        }
        other => panic!("expected success, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_eventually_satisfied() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec where x increments from 0 to 2 then stops
    // Property <>P where P == x = 2 should be satisfied WITH fairness
    // Without fairness (WF), the system could stutter forever at x=0 or x=1
    let src = r#"
---- MODULE LivenessTest ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Inc == x < 2 /\ x' = x + 1

Next == Inc \/ UNCHANGED x

\* Spec with weak fairness - ensures Inc happens when enabled
Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

\* Eventually x reaches 2
EventuallyTwo == <>(x = 2)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // First resolve the spec to get init/next/fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).unwrap();

    // Now create checker with explicit init/next
    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        invariants: vec![],
        properties: vec!["EventuallyTwo".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_fairness(resolved.fairness);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Should find 3 states: x=0, x=1, x=2
            assert_eq!(stats.states_found, 3);
        }
        other => panic!("Expected success (liveness satisfied), got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_eventually_violated() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec where x stays at 0 forever
    // Property <>P where P == x = 1 should be violated
    let src = r#"
---- MODULE LivenessViolatedTest ----
EXTENDS Integers

VARIABLE x

Init == x = 0

\* x never changes
Next == UNCHANGED x

\* Eventually x reaches 1 - but it never does!
EventuallyOne == <>(x = 1)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["EventuallyOne".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // Liveness checking requires full states

    let result = checker.check();

    match result {
        CheckResult::LivenessViolation {
            property,
            prefix: _,
            cycle,
            stats: _,
        } => {
            assert_eq!(property, "EventuallyOne");
            // The cycle should be non-empty (self-loop on x=0)
            assert!(!cycle.is_empty(), "Cycle should be non-empty");
            // Verify the cycle states all have x=0 — the system stays at x=0
            // forever (Next == UNCHANGED x), so the cycle is a self-loop on x=0.
            for (i, state) in cycle.states.iter().enumerate() {
                assert_eq!(
                    state.get("x"),
                    Some(&Value::int(0)),
                    "cycle state {} should have x=0",
                    i
                );
            }
        }
        other => panic!("Expected liveness violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_always_eventually_violated() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // System that toggles between 0 and 1 forever
    // Property []<>(x = 2) should be violated because x never reaches 2
    let src = r#"
---- MODULE AlwaysEventuallyTest ----
EXTENDS Integers

VARIABLE x

Init == x = 0

\* Toggle between 0 and 1
Next == x' = IF x = 0 THEN 1 ELSE 0

\* Infinitely often x = 2 - but it never is!
InfOftenTwo == []<>(x = 2)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["InfOftenTwo".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // Liveness checking requires full states

    let result = checker.check();

    match result {
        CheckResult::LivenessViolation {
            property,
            prefix: _,
            cycle,
            stats,
        } => {
            assert_eq!(property, "InfOftenTwo");
            assert!(!cycle.is_empty(), "Cycle should be non-empty");
            assert_eq!(stats.states_found, 2);
            // Without fairness, stuttering is allowed, so the checker may find
            // a 1-state self-loop (e.g., x=0 stuttering forever) rather than
            // a 2-state cycle through both toggle states. Either is a valid
            // counterexample to []<>(x = 2).
            let cycle_x_vals: Vec<_> = cycle
                .states
                .iter()
                .map(|s| s.get("x").unwrap().clone())
                .collect();
            assert!(
                cycle_x_vals.contains(&Value::int(0)) || cycle_x_vals.contains(&Value::int(1)),
                "cycle should contain at least one toggle state (x=0 or x=1), got {:?}",
                cycle_x_vals
            );
            // All cycle states must be in {0, 1} — the only reachable values.
            // Previously this only checked x=2 was absent, which would pass if the
            // cycle contained unexpected values like x=5.
            for val in &cycle_x_vals {
                assert!(
                    *val == Value::int(0) || *val == Value::int(1),
                    "cycle contains unexpected value {:?}, expected only x=0 or x=1",
                    val
                );
            }
        }
        other => panic!("Expected liveness violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_always_eventually_satisfied() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // System that toggles between 0 and 1 forever
    // Property []<>(x = 1) should be satisfied because x oscillates through 1
    // Requires fairness (WF) to prevent infinite stuttering at x=0
    let src = r#"
---- MODULE AlwaysEventuallySatTest ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

\* Toggle between 0 and 1
Toggle == x' = IF x = 0 THEN 1 ELSE 0

Next == Toggle

\* Spec with weak fairness - ensures Toggle happens
Spec == Init /\ [][Next]_vars /\ WF_vars(Toggle)

\* Infinitely often x = 1 - satisfied with fairness!
InfOftenOne == []<>(x = 1)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // First resolve the spec to get init/next/fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).unwrap();

    // Now create checker with explicit init/next
    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        invariants: vec![],
        properties: vec!["InfOftenOne".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_fairness(resolved.fairness);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 2);
        }
        other => panic!("Expected success (liveness satisfied), got: {:?}", other),
    }
}
