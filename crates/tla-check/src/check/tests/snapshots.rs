// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// SNAPSHOT TESTS - CheckError message format stability
// These tests ensure error messages don't change unexpectedly.
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_missing_init() {
    use insta::assert_snapshot;
    assert_snapshot!(
        "snapshot_check_error_missing_init",
        ConfigCheckError::MissingInit.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_missing_next() {
    use insta::assert_snapshot;
    assert_snapshot!(
        "snapshot_check_error_missing_next",
        ConfigCheckError::MissingNext.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_missing_invariant() {
    use insta::assert_snapshot;
    let err = ConfigCheckError::MissingInvariant("SafetyProperty".to_string());
    assert_snapshot!("snapshot_check_error_missing_invariant", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_missing_property() {
    use insta::assert_snapshot;
    let err = ConfigCheckError::MissingProperty("LivenessProperty".to_string());
    assert_snapshot!("snapshot_check_error_missing_property", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_init_not_boolean() {
    use insta::assert_snapshot;
    assert_snapshot!(
        "snapshot_check_error_init_not_boolean",
        EvalCheckError::InitNotBoolean.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_next_not_boolean() {
    use insta::assert_snapshot;
    assert_snapshot!(
        "snapshot_check_error_next_not_boolean",
        EvalCheckError::NextNotBoolean.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_invariant_not_boolean() {
    use insta::assert_snapshot;
    let err = EvalCheckError::InvariantNotBoolean("TypeOK".to_string());
    assert_snapshot!(
        "snapshot_check_error_invariant_not_boolean",
        err.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_no_variables() {
    use insta::assert_snapshot;
    assert_snapshot!(
        "snapshot_check_error_no_variables",
        ConfigCheckError::NoVariables.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_init_cannot_enumerate() {
    use insta::assert_snapshot;
    let err =
        ConfigCheckError::InitCannotEnumerate("Variable 'x' has infinite domain (Nat)".to_string());
    assert_snapshot!(
        "snapshot_check_error_init_cannot_enumerate",
        err.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_liveness() {
    use insta::assert_snapshot;
    let err = LivenessCheckError::Generic("Temporal property Liveness violated".to_string());
    assert_snapshot!("snapshot_check_error_liveness", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_liveness_runtime_failure() {
    use insta::assert_snapshot;
    let err = LivenessCheckError::RuntimeFailure(
        "Tarjan SCC algorithm invariant violation: missing node".to_string(),
    );
    assert_snapshot!(
        "snapshot_check_error_liveness_runtime_failure",
        err.to_string()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_fingerprint_overflow() {
    use insta::assert_snapshot;
    let err = InfraCheckError::FingerprintOverflow {
        dropped: 1000,
        detail: String::new(),
    };
    assert_snapshot!("snapshot_check_error_fingerprint_overflow", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_check_error_assume_false() {
    use crate::RuntimeCheckError;
    use insta::assert_snapshot;
    let err = RuntimeCheckError::AssumeFalse {
        location: "line 5, col 1 to line 5, col 20 of module Test".to_string(),
    };
    assert_snapshot!("snapshot_check_error_assume_false", err.to_string());
}
