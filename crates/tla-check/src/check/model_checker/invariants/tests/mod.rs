// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for invariant checking, state constraints, terminal state detection,
//! state tracking, and fingerprint storage error handling.
//!
//! Split from monolithic `tests.rs` (Part of #2779) into focused modules:
//! - `check_invariants` — invariant evaluation pass/fail/error
//! - `constraints` — state constraint satisfaction
//! - `terminal` — terminal state detection (operator and predicate modes)
//! - `state_tracking` — state counting, mark-seen, bulk solve
//! - `fingerprint_storage` — fingerprint overflow error precedence

mod check_invariants;
mod constraints;
mod eval_bytecode;
mod fingerprint_storage;
mod state_tracking;
mod terminal;

use super::super::{
    Arc, ArrayState, CheckError, CheckResult, Fingerprint, InsertOutcome, LookupOutcome,
    ModelChecker, State, TerminalSpec, Value,
};
use crate::config::Config;
use crate::test_support::parse_module;
use crate::InfraCheckError;
use crate::{FingerprintSet, FingerprintStorage};
use std::collections::HashSet;
use std::sync::Mutex;

/// Test-only fingerprint set that behaves like an in-memory set while
/// reporting injected storage errors via `has_errors` / `dropped_count`.
struct ErrorInjectingFingerprintSet {
    seen: Mutex<HashSet<crate::state::Fingerprint>>,
    dropped: usize,
}

impl ErrorInjectingFingerprintSet {
    fn new(dropped: usize) -> Self {
        Self {
            seen: Mutex::new(HashSet::new()),
            dropped,
        }
    }
}

impl tla_mc_core::FingerprintSet<crate::state::Fingerprint> for ErrorInjectingFingerprintSet {
    fn insert_checked(&self, fp: crate::state::Fingerprint) -> InsertOutcome {
        if self
            .seen
            .lock()
            .expect("error-injecting set lock poisoned")
            .insert(fp)
        {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fp: crate::state::Fingerprint) -> LookupOutcome {
        if self
            .seen
            .lock()
            .expect("error-injecting set lock poisoned")
            .contains(&fp)
        {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        self.seen
            .lock()
            .expect("error-injecting set lock poisoned")
            .len()
    }

    fn has_errors(&self) -> bool {
        true
    }

    fn dropped_count(&self) -> usize {
        self.dropped
    }
}

impl FingerprintSet for ErrorInjectingFingerprintSet {}

fn inject_fingerprint_storage_error(mc: &mut ModelChecker<'_>, dropped: usize) {
    let storage = Arc::new(ErrorInjectingFingerprintSet::new(dropped)) as Arc<dyn FingerprintSet>;
    mc.set_fingerprint_storage(storage);
}

fn assert_fingerprint_overflow_with_dropped(result: CheckResult, expected_dropped: usize) {
    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => {
            assert_eq!(
                dropped, expected_dropped,
                "storage error should preserve injected dropped count"
            );
        }
        other => {
            panic!("expected FingerprintStorageOverflow error, got {other:?}");
        }
    }
}
