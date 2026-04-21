// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel on-the-fly liveness regressions.

use super::*;
use crate::check::PropertyViolationKind;
use crate::config::{ConstantValue, LivenessExecutionMode};
use crate::Value;

const PARALLEL_ON_THE_FLY_VIOLATION_SPEC: &str = r#"
---- MODULE ParallelOnTheFlyViolation ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == UNCHANGED x
EventuallyOne == <>(x = 1)
====
"#;

const PARALLEL_ON_THE_FLY_MIXED_SPEC: &str = r#"
---- MODULE ParallelOnTheFlyMixed ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Mixed == [](x < 1) /\ <>(x = 2)
====
"#;

const PARALLEL_ON_THE_FLY_VIEW_SPEC: &str = r#"
---- MODULE ParallelOnTheFlyView ----
EXTENDS Integers

VARIABLES x, y

Init == x = 0 /\ y = 0
Next == /\ x' = x
        /\ y' = 1 - y
View == <<x>>
EventuallyOne == <>(x = 1)
====
"#;

const PARALLEL_ON_THE_FLY_SYMMETRY_SPEC: &str = r#"
---- MODULE ParallelOnTheFlySymmetry ----
EXTENDS TLC, Integers

CONSTANT Procs
VARIABLE owner

Init == owner \in Procs
Next == UNCHANGED owner
StableOwner == <>[](owner \in Procs)
Sym == Permutations(Procs)
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_on_the_fly_liveness_violation_detected() {
    let _serial = super::super::acquire_interner_lock();
    let module = parse_module(PARALLEL_ON_THE_FLY_VIOLATION_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyOne".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_store_states(true);
    match checker.check() {
        CheckResult::LivenessViolation {
            property, cycle, ..
        } => {
            assert_eq!(property, "EventuallyOne");
            assert!(
                !cycle.is_empty(),
                "parallel on-the-fly violation should include a witness cycle"
            );
        }
        other => panic!("expected parallel on-the-fly liveness violation, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_on_the_fly_mixed_property_checks_safety_first() {
    let _serial = super::super::acquire_interner_lock();
    let module = parse_module(PARALLEL_ON_THE_FLY_MIXED_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Mixed".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        } => {
            assert_eq!(property, "Mixed");
            assert_eq!(kind, PropertyViolationKind::StateLevel);
            assert!(
                !trace.is_empty(),
                "mixed on-the-fly property should return a safety witness"
            );
            assert_eq!(trace.states[0].get("x"), Some(&Value::int(1)));
        }
        other => panic!("expected mixed on-the-fly safety violation, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_on_the_fly_liveness_supports_view_fingerprints() {
    let _serial = super::super::acquire_interner_lock();
    let module = parse_module(PARALLEL_ON_THE_FLY_VIEW_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyOne".to_string()],
        view: Some("View".to_string()),
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::LivenessViolation {
            property, cycle, ..
        } => {
            assert_eq!(property, "EventuallyOne");
            assert!(
                !cycle.is_empty(),
                "parallel VIEW on-the-fly liveness should produce a counterexample cycle"
            );
            for state in &cycle.states {
                assert_eq!(state.get("x"), Some(&Value::int(0)));
            }
        }
        other => panic!("expected parallel VIEW on-the-fly violation, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_on_the_fly_liveness_supports_symmetry_configs() {
    let _serial = super::super::acquire_interner_lock();
    let module = parse_module(PARALLEL_ON_THE_FLY_SYMMETRY_SPEC);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["StableOwner".to_string()],
        symmetry: Some("Sym".to_string()),
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "symmetry should collapse owner states"
            );
        }
        other => panic!("expected parallel on-the-fly symmetry success, got: {other:?}"),
    }
}
