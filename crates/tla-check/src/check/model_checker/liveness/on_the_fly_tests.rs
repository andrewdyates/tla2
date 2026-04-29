// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::ModelChecker;
use crate::check::{resolve_spec_from_config, CheckResult};
use crate::{Config, LivenessExecutionMode, Value};
use tla_core::{lower, parse_to_syntax_tree, FileId};

const ON_THE_FLY_SUCCESS_SPEC: &str = r#"
---- MODULE OnTheFlyLivenessSuccess ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0
Inc == x < 2 /\ x' = x + 1
Next == Inc \/ UNCHANGED x
Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)
EventuallyTwo == <>(x = 2)
====
"#;

const ON_THE_FLY_VIOLATION_SPEC: &str = r#"
---- MODULE OnTheFlyLivenessViolation ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == UNCHANGED x
EventuallyOne == <>(x = 1)
====
"#;

const ON_THE_FLY_UNSUPPORTED_SPEC: &str = r#"
---- MODULE OnTheFlyUnsupported ----
EXTENDS Integers

VARIABLE x

View == x
Init == x = 0
Next == UNCHANGED x
EventuallyZero == <>(x = 0)
====
"#;

const ON_THE_FLY_VIEW_SPEC: &str = r#"
---- MODULE OnTheFlyView ----
EXTENDS Integers

VARIABLES x, y

Init == x = 0 /\ y = 0
Next == /\ x' = x
        /\ y' = 1 - y
View == <<x>>
EventuallyOne == <>(x = 1)
====
"#;

const ON_THE_FLY_SYMMETRY_SPEC: &str = r#"
---- MODULE OnTheFlySymmetry ----
EXTENDS TLC, Integers

CONSTANT Procs
VARIABLE owner

Init == owner \in Procs
Next == UNCHANGED owner
StableOwner == <>[](owner \in Procs)
Sym == Permutations(Procs)
====
"#;

const ON_THE_FLY_MIXED_SAFETY_SPEC: &str = r#"
---- MODULE OnTheFlyMixedSafety ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0
Step == x < 1 /\ x' = x + 1
Next == Step \/ UNCHANGED x
InitMustBeOne == x = 1
StepMustSkip == [][x' = x + 2]_vars
MixedInitAndLive == (x = 1) /\ <>(x = 1)
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_liveness_succeeds_without_cached_successor_graph() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_SUCCESS_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).expect("SPECIFICATION resolves");
    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["EventuallyTwo".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    checker.set_fairness(resolved.fairness);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "expected x=0,1,2 to be reachable");
        }
        other => panic!("expected success from on-the-fly liveness, got {other:?}"),
    }

    assert_eq!(
        checker.liveness_cache.successors.len(),
        0,
        "on-the-fly mode must not retain the BFS successor graph"
    );
    assert_eq!(
        checker.liveness_cache.successors.total_successors(),
        0,
        "on-the-fly mode must not record any cached liveness edges"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_liveness_reports_violation_in_fp_only_mode() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_VIOLATION_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyOne".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);

    let result = checker.check();
    match result {
        CheckResult::LivenessViolation {
            property,
            prefix: _,
            cycle,
            ..
        } => {
            assert_eq!(property, "EventuallyOne");
            assert!(
                !cycle.is_empty(),
                "violating on-the-fly run should include a witness cycle"
            );
            for state in &cycle.states {
                assert_eq!(state.get("x"), Some(&Value::int(0)));
            }
        }
        other => panic!("expected on-the-fly liveness violation, got {other:?}"),
    }

    assert_eq!(
        checker.liveness_cache.successors.len(),
        0,
        "on-the-fly violation runs must also avoid caching the BFS successor graph"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_liveness_supports_view_fingerprints() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_VIEW_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyOne".to_string()],
        view: Some("View".to_string()),
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::LivenessViolation {
            property, cycle, ..
        } => {
            assert_eq!(property, "EventuallyOne");
            assert!(
                !cycle.is_empty(),
                "VIEW on-the-fly liveness should produce a counterexample cycle"
            );
            for state in &cycle.states {
                assert_eq!(state.get("x"), Some(&Value::int(0)));
            }
        }
        other => panic!("expected VIEW on-the-fly liveness violation, got {other:?}"),
    }
}

/// Part of #3706: Verify POR is accepted with on-the-fly liveness.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn model_checker_accepts_por_with_on_the_fly_liveness() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_UNSUPPORTED_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyZero".to_string()],
        por_enabled: true,
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    // POR should no longer be rejected — the checker proceeds normally.
    // This spec has `UNCHANGED x` as Next, so x stays 0 forever, satisfying <>(x=0).
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "single-state UNCHANGED spec should have exactly 1 state"
            );
        }
        other => {
            panic!("POR with on-the-fly liveness should succeed (Part of #3706), got {other:?}")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_liveness_supports_symmetry_configs() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_SYMMETRY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
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
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "symmetry should collapse owner states"
            );
        }
        other => panic!("expected on-the-fly symmetry liveness success, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_safety_only_property_reports_state_level_violation() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_MIXED_SAFETY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["InitMustBeOne".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        } => {
            assert_eq!(property, "InitMustBeOne");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                1,
                "init violation should be single-state"
            );
            assert_eq!(trace.states[0].get("x"), Some(&Value::int(0)));
        }
        other => panic!("expected state-level property violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_safety_only_property_reports_action_level_violation() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_MIXED_SAFETY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["StepMustSkip".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        } => {
            assert_eq!(property, "StepMustSkip");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::ActionLevel);
            assert_eq!(
                trace.states.len(),
                2,
                "action violation should include both states"
            );
            assert_eq!(trace.states[0].get("x"), Some(&Value::int(0)));
            assert_eq!(trace.states[1].get("x"), Some(&Value::int(1)));
        }
        other => panic!("expected action-level property violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn on_the_fly_mixed_property_checks_safety_parts_before_temporal_core() {
    let tree = parse_to_syntax_tree(ON_THE_FLY_MIXED_SAFETY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["MixedInitAndLive".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        } => {
            assert_eq!(property, "MixedInitAndLive");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                1,
                "mixed init violation should short-circuit"
            );
            assert_eq!(trace.states[0].get("x"), Some(&Value::int(0)));
        }
        other => panic!("expected mixed state-level property violation, got {other:?}"),
    }
}
