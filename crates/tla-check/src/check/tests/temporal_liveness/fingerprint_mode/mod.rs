// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod implied_actions;
mod liveness_correctness;

const FP_ONLY_NON_INIT_CYCLE_SPEC: &str = r#"
---- MODULE FpOnlyNonInitCycle ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' = 1
    \/ /\ x = 1
       /\ x' = 2
    \/ /\ x = 2
       /\ x' = 1

AlwaysReturnZero == []<>(x = 0)
====
"#;

fn run_explicit_fp_only_property_check(src: &str, property: &str) -> CheckResult {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    checker.check()
}

fn trace_x_values(trace: &Trace) -> Vec<Value> {
    trace
        .states
        .iter()
        .map(|state| state.get("x").expect("trace state should have x").clone())
        .collect()
}

/// Part of #3175: fingerprint-only mode checks liveness by default.
///
/// `ModelChecker::new()` and the public `check_module()` helper should both
/// enable BFS-time liveness caching whenever temporal properties exist. A
/// violated eventuality must therefore report `LivenessViolation` even when
/// `store_full_states` remains at its default `false`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_only_mode_checks_liveness_by_default() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec where x stays at 0 forever — <>(x = 1) is violated.
    let src = r#"
---- MODULE FingerprintLiveness ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == UNCHANGED x

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

    for result in [checker.check(), crate::check_module(&module, &config)] {
        match result {
            CheckResult::LivenessViolation {
                property,
                cycle,
                stats,
                ..
            } => {
                assert_eq!(property, "EventuallyOne");
                assert_eq!(stats.states_found, 1);
                assert!(
                    !cycle.is_empty(),
                    "fp-only liveness violation should include a non-empty cycle"
                );
            }
            other => panic!("Expected LivenessViolation in default fp-only mode, got: {other:?}"),
        }
    }
}
