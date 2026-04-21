// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #1698: nested []<> extraction in liveness plan decomposition.
//!
//! Verifies that extract_nested_ae correctly handles formulas with nested
//! always-eventually patterns, and that no constraints are silently dropped
//! during plan decomposition.

use tla_check::Config;
use tla_check::{resolve_spec_from_config, CheckResult};
use tla_core::{lower, parse_to_syntax_tree, FileId};

mod common;

/// Verifies that a spec with WF (which expands to []<>(...)) correctly
/// detects a liveness violation. The []<> pattern exercises the
/// extract_nested_ae path in plan.rs. If extraction silently dropped
/// the AE constraint, the checker would report Satisfied (false negative).
///
/// Spec: x increments 0→1→2 via Inc (guarded by x < 2), then Inc is disabled.
/// WF_vars(Inc) ensures Inc fires when enabled. Once x=2, the system stutters.
/// Property <>(x = 3) is violated: x never reaches 3.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_nested_ae_wf_violation_detected() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessNestedAEViolation ----
EXTENDS Integers

VARIABLE x
vars == <<x>>
Init == x = 0
Inc == x < 2 /\ x' = x + 1
Next == Inc \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

\* x reaches 2 and stays there. <>(x=3) is violated.
Prop == <>(x = 3)

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("failed to parse module");

    // Resolve the spec to get init/next/fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree)
        .expect("invariant: spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // Required for liveness checking
    checker.set_fairness(resolved.fairness);
    let result = checker.check();

    match &result {
        CheckResult::LivenessViolation {
            property, stats, ..
        } => {
            // Expected: x goes 0→1→2 and stays at 2 forever. <>(x=3) violated.
            assert_eq!(property, "Prop", "violated property name should match");
            assert_eq!(
                stats.states_found, 3,
                "spec should explore exactly 3 states (x=0, x=1, x=2)"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation but got Success — \
                 the liveness checker may be silently dropping AE constraints \
                 from the WF expansion (see #1698)"
            );
        }
        other => {
            panic!("expected LivenessViolation, got: {other:?}");
        }
    }
}

/// Verifies that a spec with a satisfied liveness property containing
/// weak fairness ([]<> pattern) reports Success. Exercises the same
/// extract_nested_ae path but with a satisfying model.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_nested_ae_wf_satisfaction() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessNestedAESatisfied ----

VARIABLE x
vars == <<x>>
Init == x \in {0, 1}
Next == IF x = 0 THEN x' = 1 ELSE x' = 0
Toggle == IF x = 0 THEN x' = 1 ELSE x' = 0
Spec == Init /\ [][Next]_vars /\ WF_vars(Toggle)

\* This should be satisfied: with WF, Toggle fires infinitely often,
\* so x = 1 occurs infinitely often.
Prop == []<>(x = 1)

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("failed to parse module");

    // Resolve the spec to get init/next/fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree)
        .expect("invariant: spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // Required for liveness checking
    checker.set_fairness(resolved.fairness);
    let result = checker.check();

    match &result {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found >= 2,
                "expected at least 2 states (x=0, x=1), got {}",
                stats.states_found
            );
        }
        CheckResult::LivenessViolation { .. } => {
            panic!(
                "expected Success but got LivenessViolation — \
                 the liveness checker may be over-constraining AE checks \
                 from the WF expansion"
            );
        }
        other => {
            panic!("expected Success, got: {other:?}");
        }
    }
}
