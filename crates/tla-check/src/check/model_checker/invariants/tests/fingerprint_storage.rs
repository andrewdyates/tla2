// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for fingerprint storage error precedence: overflow must outrank
//! invariant violations, deadlock, state limits, and liveness errors.

use super::*;
use crate::InfraCheckError;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_fingerprint_storage_errors_none_initially() {
    let module = parse_module(
        r#"
---- MODULE FpOk ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mc = ModelChecker::new(&module, &config);
    assert!(mc.check_fingerprint_storage_errors().is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_reports_fingerprint_overflow_as_error() {
    let module = parse_module(
        r#"
---- MODULE FpOverflow ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 4 THEN 0 ELSE x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_deadlock_check(false);

    // Tiny mmap storage to force overflow and verify we fail hard by default.
    let mmap_storage =
        FingerprintStorage::mmap(2, None).expect("failed to create mmap fingerprint storage");
    mc.set_fingerprint_storage(Arc::new(mmap_storage) as Arc<dyn FingerprintSet>);

    match mc.check() {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => {
            assert!(dropped > 0, "overflow error should report dropped states");
        }
        other => {
            panic!("expected FingerprintStorageOverflow error, got {other:?}");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_reports_fingerprint_overflow_as_error_in_full_state_mode() {
    let module = parse_module(
        r#"
---- MODULE FpOverflowFullState ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 4 THEN 0 ELSE x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_deadlock_check(false);
    mc.set_store_states(true);

    // Tiny mmap storage to force overflow while exercising run_bfs_full.rs.
    let mmap_storage =
        FingerprintStorage::mmap(2, None).expect("failed to create mmap fingerprint storage");
    mc.set_fingerprint_storage(Arc::new(mmap_storage) as Arc<dyn FingerprintSet>);

    match mc.check() {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => {
            assert!(dropped > 0, "overflow error should report dropped states");
        }
        other => {
            panic!("expected FingerprintStorageOverflow error, got {other:?}");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_prioritizes_fingerprint_overflow_before_liveness_in_full_state_mode() {
    let module = parse_module(
        r#"
---- MODULE FpOverflowBeforeLiveness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 4 THEN 0 ELSE x + 1
EventuallyNever == <>(x = 99)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyNever".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_deadlock_check(false);
    mc.set_store_states(true);

    // Tiny mmap storage to force overflow while liveness work is configured.
    let mmap_storage =
        FingerprintStorage::mmap(2, None).expect("failed to create mmap fingerprint storage");
    mc.set_fingerprint_storage(Arc::new(mmap_storage) as Arc<dyn FingerprintSet>);

    match mc.check() {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => {
            assert!(dropped > 0, "overflow error should report dropped states");
        }
        other => {
            panic!("expected FingerprintStorageOverflow error, got {other:?}");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_prioritizes_fingerprint_overflow_before_deadlock() {
    let module = parse_module(
        r#"
---- MODULE FpOverflowBeforeDeadlock ----
VARIABLE x
Init == x = 0
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let dropped = 17;
    inject_fingerprint_storage_error(&mut mc, dropped);

    assert_fingerprint_overflow_with_dropped(mc.check(), dropped);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_prioritizes_fingerprint_overflow_before_state_limit_notrace() {
    let module = parse_module(
        r#"
---- MODULE FpOverflowBeforeStateLimit ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_store_states(false);
    mc.set_max_states(1);
    let dropped = 23;
    inject_fingerprint_storage_error(&mut mc, dropped);

    assert_fingerprint_overflow_with_dropped(mc.check(), dropped);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_prioritizes_fingerprint_overflow_before_deferred_invariant_violation() {
    let module = parse_module(
        r#"
---- MODULE FpOverflowBeforeDeferredViolation ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
Safe == x = 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_continue_on_error(true);
    mc.set_deadlock_check(false);
    let dropped = 31;
    inject_fingerprint_storage_error(&mut mc, dropped);

    assert_fingerprint_overflow_with_dropped(mc.check(), dropped);
}

/// Part of #1801: Verify that storage-error precedence applies to immediate
/// invariant violations (non-deferred, continue_on_error=false). Before the
/// fix, `handle_invariant_violation` returned `InvariantViolation` directly
/// without routing through `finalize_terminal_result`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_prioritizes_fingerprint_overflow_before_immediate_invariant_violation() {
    // Spec where x=1 (successor of Init) always violates Safe.
    // With continue_on_error=false (default), the violation is immediate.
    let module = parse_module(
        r#"
---- MODULE FpOverflowBeforeImmediateViolation ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
Safe == x = 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_deadlock_check(false);
    // Default: continue_on_error=false — violation returns immediately
    let dropped = 19;
    inject_fingerprint_storage_error(&mut mc, dropped);

    assert_fingerprint_overflow_with_dropped(mc.check(), dropped);
}

/// Part of #1801: Verify storage-error precedence on initial-state violations.
/// Init produces a state that immediately violates the invariant.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_prioritizes_fingerprint_overflow_before_init_state_violation() {
    // Invariant FALSE: every initial state violates immediately.
    let module = parse_module(
        r#"
---- MODULE FpOverflowBeforeInitViolation ----
VARIABLE x
Init == x = 1
Next == x' = x
AlwaysFalse == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AlwaysFalse".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_deadlock_check(false);
    let dropped = 47;
    inject_fingerprint_storage_error(&mut mc, dropped);

    assert_fingerprint_overflow_with_dropped(mc.check(), dropped);
}
