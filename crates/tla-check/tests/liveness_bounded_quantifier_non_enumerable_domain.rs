// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_check::Config;
use tla_check::LivenessCheckError;
use tla_check::{CheckError, CheckResult};

mod common;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_errors_on_bounded_quantifier_non_enumerable_domain() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessBoundedQuantifierNonEnumerableDomain ----
EXTENDS Sequences, Naturals

VARIABLE x
Init == x = 0
Next == x' = x

Prop == \E y \in Seq({1}) : <>TRUE

====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Liveness(LivenessCheckError::CannotHandleFormula { location, reason }) => {
                assert!(location.contains("bytes"));
                assert!(
                    location.contains("of module LivenessBoundedQuantifierNonEnumerableDomain"),
                    "unexpected location: {location}"
                );
                let reason = reason.expect("expected reason for cannot-handle-formula error");
                // Part of #1433: error message now says "iteration failed" with
                // preserved iterator error details instead of generic "not enumerable".
                assert!(
                    reason.contains("bounded-quantifier domain")
                        && reason.contains("iteration failed"),
                    "expected bounded-quantifier iteration failure, got: {reason}"
                );
                assert!(
                    reason.contains("Type error: expected Set"),
                    "expected preserved iterator error details, got: {reason}"
                );
            }
            other => panic!("expected TlcLiveCannotHandleFormula, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_errors_on_bounded_quantifier_non_set_domain() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessBoundedQuantifierNonSetDomain ----

VARIABLE x
Init == x = 0
Next == x' = x

\* Domain is not a set; TLC errors during bounded-quantifier context enumeration.
Prop == \E y \in 3 : <>TRUE

====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Liveness(LivenessCheckError::CannotHandleFormula { location, reason }) => {
                assert!(location.contains("bytes"));
                assert!(
                    location.contains("of module LivenessBoundedQuantifierNonSetDomain"),
                    "unexpected location: {location}"
                );
                let reason = reason.expect("expected reason for cannot-handle-formula error");
                // Part of #1433: error message now says "iteration failed" with
                // preserved iterator error details instead of generic "not enumerable".
                assert!(
                    reason.contains("bounded-quantifier domain")
                        && reason.contains("iteration failed"),
                    "expected bounded-quantifier iteration failure, got: {reason}"
                );
                assert!(
                    reason.contains("Type error: expected Set"),
                    "expected preserved iterator error details, got: {reason}"
                );
            }
            other => panic!("expected TlcLiveCannotHandleFormula, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_errors_on_unbounded_quantifier_over_temporal_body() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessUnboundedQuantifierTemporal ----

VARIABLE x
Init == x = 0
Next == x' = x

\* Unbounded quantifier must be treated like TLC's "cannot handle formula" when temporal-level.
Prop == \E y : <>TRUE

====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Liveness(LivenessCheckError::CannotHandleFormula { location, reason }) => {
                assert!(location.contains("bytes"));
                assert!(
                    location.contains("of module LivenessUnboundedQuantifierTemporal"),
                    "unexpected location: {location}"
                );
                let reason = reason.expect("expected reason for cannot-handle-formula error");
                assert!(
                    reason.contains("unbounded quantifier"),
                    "expected unbounded quantifier reason, got: {reason}"
                );
            }
            other => panic!("expected TlcLiveCannotHandleFormula, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}
