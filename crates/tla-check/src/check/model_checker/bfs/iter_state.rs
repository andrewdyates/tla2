// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-iteration BFS state guard (RAII).
//!
//! Wraps the current state's fingerprint and array, ensuring that
//! `return_to()` is called exactly once before the guard is dropped.
//! Part of #2677 Phase 1, extracted from `engine.rs` as part of #2356.

use super::super::{ArrayState, CheckError, CheckResult, Fingerprint, ModelChecker};
use super::storage_modes::BfsStorage;

/// Per-iteration state guard for the BFS loop.
///
/// Wraps the current state's fingerprint and array, ensuring that
/// `return_to()` is called exactly once before the guard is dropped.
/// A `debug_assert` in `Drop` catches missed returns during development.
///
/// Part of #2677 Phase 1.
pub(in crate::check::model_checker::bfs) struct BfsIterState {
    fp: Fingerprint,
    current_array: Option<ArrayState>,
}

impl BfsIterState {
    pub(in crate::check::model_checker::bfs) fn new(
        fp: Fingerprint,
        current_array: ArrayState,
    ) -> Self {
        Self {
            fp,
            current_array: Some(current_array),
        }
    }

    /// Access the fingerprint (Copy).
    pub(in crate::check::model_checker::bfs) fn fp(&self) -> Fingerprint {
        self.fp
    }

    /// Borrow the current array state.
    pub(in crate::check::model_checker::bfs) fn array(&self) -> &ArrayState {
        self.current_array
            .as_ref()
            .expect("BfsIterState: array already returned")
    }

    /// Return the current state to storage, consuming the array.
    /// Must be called exactly once per iteration.
    pub(in crate::check::model_checker::bfs) fn return_to<S: BfsStorage>(
        &mut self,
        storage: &mut S,
        checker: &mut ModelChecker<'_>,
    ) {
        let array = self
            .current_array
            .take()
            .expect("BfsIterState: return_to called twice");
        storage.return_current(self.fp, array, checker);
    }
}

impl Drop for BfsIterState {
    fn drop(&mut self) {
        // Skip the assertion during unwinding to avoid double-panic → SIGABRT.
        // A double panic kills the entire test runner (Part of #4067).
        if !std::thread::panicking() {
            debug_assert!(
                self.current_array.is_none(),
                "BfsIterState dropped without calling return_to — storage leak (fp={:?})",
                self.fp
            );
        }
    }
}

use super::super::check_error_to_result;

impl ModelChecker<'_> {
    /// Handle a BFS error: update coverage, return current state, produce result.
    ///
    /// Bundles the 3-line `update_coverage_totals + return_current + check_error_to_result`
    /// pattern that appears at multiple sites in the BFS successor processing.
    ///
    /// Part of #2677 Phase 1.
    pub(in crate::check::model_checker::bfs) fn bfs_error_return<S: BfsStorage>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        error: CheckError,
    ) -> CheckResult {
        self.update_coverage_totals();
        iter_state.return_to(storage, self);
        check_error_to_result(error, &self.stats)
    }
}
