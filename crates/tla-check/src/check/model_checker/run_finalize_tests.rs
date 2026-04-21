// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for finish_check_after_bfs storage-error gate (#2164).

use super::*;
use crate::config::Config;
use crate::storage::{FingerprintSet, InsertOutcome, LookupOutcome};
use crate::test_support::parse_module;
use crate::CheckError;
use crate::Fingerprint;
use crate::InfraCheckError;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

/// Test-only fingerprint storage that flips to `has_errors = true` after
/// a configured number of has_errors() checks.
struct FlippingErrorFingerprintSet {
    seen: dashmap::DashSet<Fingerprint>,
    has_errors_calls: AtomicUsize,
    error_after_calls: usize,
    dropped: usize,
}

impl FlippingErrorFingerprintSet {
    fn new(error_after_calls: usize, dropped: usize) -> Self {
        Self {
            seen: dashmap::DashSet::new(),
            has_errors_calls: AtomicUsize::new(0),
            error_after_calls,
            dropped,
        }
    }

    fn has_errors_call_count(&self) -> usize {
        self.has_errors_calls.load(Ordering::Acquire)
    }
}

impl tla_mc_core::FingerprintSet<Fingerprint> for FlippingErrorFingerprintSet {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        if self.seen.insert(fp) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        if self.seen.contains(&fp) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        self.seen.len()
    }

    fn has_errors(&self) -> bool {
        let call = self.has_errors_calls.fetch_add(1, Ordering::AcqRel);
        call >= self.error_after_calls
    }

    fn dropped_count(&self) -> usize {
        self.dropped
    }
}

impl FingerprintSet for FlippingErrorFingerprintSet {}

fn assert_fingerprint_overflow_with_dropped(result: CheckResult, expected_dropped: usize) {
    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => {
            assert_eq!(
                dropped, expected_dropped,
                "storage error should preserve injected dropped count",
            );
        }
        other => {
            panic!("expected FingerprintStorageOverflow error, got {other:?}");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn finish_check_after_bfs_liveness_result_rechecked_for_storage_errors() {
    let module = parse_module(
        r#"
---- MODULE LivenessFinalizeGate ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Prop == []<>(x = 2)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let storage = Arc::new(FlippingErrorFingerprintSet::new(1, 17));
    checker.set_fingerprint_storage(storage.clone() as Arc<dyn FingerprintSet>);

    let result = checker.check();
    assert_fingerprint_overflow_with_dropped(result, 17);
    assert!(
        storage.has_errors_call_count() >= 2,
        "expected terminal gate to re-check storage errors after liveness result",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn finish_check_after_bfs_postcondition_result_rechecked_for_storage_errors() {
    let module = parse_module(
        r#"
---- MODULE PostconditionFinalizeGate ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Post == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("Post".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    let storage = Arc::new(FlippingErrorFingerprintSet::new(1, 23));
    checker.set_fingerprint_storage(storage.clone() as Arc<dyn FingerprintSet>);

    let result = checker.check();
    assert_fingerprint_overflow_with_dropped(result, 23);
    assert!(
        storage.has_errors_call_count() >= 2,
        "expected terminal gate to re-check storage errors after postcondition result",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn finish_check_after_bfs_success_rechecked_for_storage_errors() {
    let module = parse_module(
        r#"
---- MODULE SuccessFinalizeGate ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    let storage = Arc::new(FlippingErrorFingerprintSet::new(1, 31));
    checker.set_fingerprint_storage(storage.clone() as Arc<dyn FingerprintSet>);

    let result = checker.check();
    assert_fingerprint_overflow_with_dropped(result, 31);
    assert!(
        storage.has_errors_call_count() >= 2,
        "expected terminal gate to re-check storage errors before success return",
    );
}
