// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for #3401: promoted PROPERTY invariants must not be
//! skipped on the default sequential TIR path.

mod common;

use common::{parse_module, EnvVarGuard};
use ntest::timeout;
use tla_check::{check_module, CheckResult, Config, PropertyViolationKind, Value};

fn run_promoted_property_check(spec: &str) -> CheckResult {
    let _tir_eval = EnvVarGuard::remove("TLA2_TIR_EVAL");
    let _tir_parity = EnvVarGuard::remove("TLA2_TIR_PARITY");
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        properties: vec!["AlwaysSafe".to_string()],
        ..Default::default()
    };

    check_module(&module, &config)
}

fn run_eval_state_property_check(spec: &str) -> CheckResult {
    let _tir_eval = EnvVarGuard::remove("TLA2_TIR_EVAL");
    let _tir_parity = EnvVarGuard::remove("TLA2_TIR_PARITY");
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysEnabled".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    check_module(&module, &config)
}

#[test]
#[timeout(10000)]
fn test_bug_3401_promoted_property_invariant_checked_on_initial_state() {
    let spec = r#"
---- MODULE PromotedPropertyInit3401 ----
EXTENDS Integers

VARIABLE x

Init == x = 2
Next == UNCHANGED x

TypeOK == x \in 0..2
Safe == x <= 1
AlwaysSafe == []Safe
====
"#;

    // Part of #3354: simplified from legacy-vs-TIR comparison to direct check.
    match run_promoted_property_check(spec) {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats,
            ..
        } => {
            assert_eq!(property, "AlwaysSafe");
            assert_eq!(kind, PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                1,
                "init violation should report one state"
            );
            assert_eq!(
                stats.states_found, 0,
                "init violation should fail before admitting any distinct state"
            );
            assert_eq!(trace.states[0].get("x"), Some(&Value::int(2)));
        }
        other => panic!("expected promoted PROPERTY init violation, got {other:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_bug_3401_promoted_property_invariant_checked_on_successor_state() {
    let spec = r#"
---- MODULE PromotedPropertySucc3401 ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

TypeOK == x \in 0..2
Safe == x <= 1
AlwaysSafe == []Safe
====
"#;

    // Part of #3354: simplified from legacy-vs-TIR comparison to direct check.
    match run_promoted_property_check(spec) {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats,
            ..
        } => {
            assert_eq!(property, "AlwaysSafe");
            assert_eq!(kind, PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                3,
                "successor violation should include the full 0 -> 1 -> 2 trace"
            );
            assert_eq!(
                stats.states_found, 3,
                "successor violation should stop after admitting x=2"
            );
            let last = trace
                .states
                .last()
                .expect("successor violation should have trace");
            assert_eq!(last.get("x"), Some(&Value::int(2)));
        }
        other => panic!("expected promoted PROPERTY successor violation, got {other:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_bug_3401_eval_state_promoted_property_checked_on_initial_state() {
    let spec = r#"
---- MODULE PromotedEvalPropertyInit3401 ----
VARIABLE x

Init == x = 0
Next == FALSE

AlwaysEnabled == []ENABLED Next
====
"#;

    // Part of #3354: simplified from legacy-vs-TIR comparison to direct check.
    match run_eval_state_property_check(spec) {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats,
            ..
        } => {
            assert_eq!(property, "AlwaysEnabled");
            assert_eq!(kind, PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                1,
                "eval-only init violation should report one state"
            );
            assert_eq!(
                stats.states_found, 0,
                "eval-only init violation should fail before admitting any distinct state"
            );
            assert_eq!(trace.states[0].get("x"), Some(&Value::int(0)));
        }
        other => panic!("expected eval-only promoted PROPERTY init violation, got {other:?}"),
    }
}
