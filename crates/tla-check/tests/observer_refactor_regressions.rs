// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for the sequential BFS observer refactor.

mod common;

use common::parse_module;
use ntest::timeout;
use tla_check::{CheckResult, Config, ModelChecker};

fn observer_constraint_spec() -> tla_core::ast::Module {
    parse_module(
        r#"
---- MODULE ObserverRefactorRegression ----
EXTENDS Naturals, TLC

VARIABLE x

Init == x = 0
Next == x' = x + 1
DepthBound == TLCGet("level") <= 10
Safe == x < 2
View == x

====
"#,
    )
}

#[test]
#[timeout(30_000)]
fn diff_batch_counts_constrained_transition_before_invariant_stop() {
    let module = observer_constraint_spec();
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["DepthBound".to_string()],
        invariants: vec!["Safe".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let result = ModelChecker::new(&module, &config).check();
    match result {
        CheckResult::InvariantViolation { stats, .. } => {
            assert_eq!(
                stats.transitions, 2,
                "diff batch path should count the violating transition before the invariant stop"
            );
        }
        other => panic!("expected invariant violation from diff batch path, got {other:?}"),
    }
}

#[test]
#[timeout(30_000)]
fn full_state_batch_counts_constrained_transition_before_invariant_stop() {
    let module = observer_constraint_spec();
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["DepthBound".to_string()],
        invariants: vec!["Safe".to_string()],
        view: Some("View".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let result = ModelChecker::new(&module, &config).check();
    match result {
        CheckResult::InvariantViolation { stats, .. } => {
            assert_eq!(
                stats.transitions, 2,
                "full-state batch path should count the violating transition before the invariant stop"
            );
        }
        other => panic!("expected invariant violation from full-state batch path, got {other:?}"),
    }
}
