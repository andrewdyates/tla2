// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Common configuration interface for model checkers.
//!
//! The [`CheckerConfigurable`] trait provides a uniform API for configuring
//! both `ModelChecker` and `ParallelChecker`, allowing `AdaptiveChecker`
//! to apply settings through a single code path.

use crate::check::{CheckError, ModelChecker, ProgressCallback, ResolvedSpec};
use crate::collision_detection::CollisionCheckMode;
use crate::parallel::ParallelChecker;
use crate::resource_budget::ResourceBudget;
use crate::spec_formula::FairnessConstraint;
use crate::storage::FingerprintSet;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tla_core::FileId;

/// Common configuration interface for model checkers.
///
/// Implemented by both `ModelChecker` and `ParallelChecker` so that
/// `AdaptiveChecker::apply_common_config` can configure either type through
/// a single code path, eliminating the config propagation duplication that
/// previously caused bugs (#2762, #2772).
pub(crate) trait CheckerConfigurable {
    fn register_file_path(&mut self, file_id: FileId, path: PathBuf);
    fn register_inline_next(&mut self, resolved: &ResolvedSpec) -> Result<(), CheckError>;
    fn set_deadlock_check(&mut self, check: bool);
    fn set_stuttering_allowed(&mut self, allowed: bool);
    fn set_continue_on_error(&mut self, continue_on_error: bool);
    fn set_store_states(&mut self, store: bool);
    fn set_auto_create_trace_file(&mut self, auto_create: bool);
    fn set_fairness(&mut self, fairness: Vec<FairnessConstraint>);
    fn set_fingerprint_storage(&mut self, storage: Arc<dyn FingerprintSet>);
    fn set_max_states(&mut self, limit: usize);
    fn set_max_depth(&mut self, limit: usize);
    fn set_memory_limit(&mut self, limit_bytes: usize);
    fn set_disk_limit(&mut self, limit_bytes: usize);
    // AdaptiveChecker does not yet own checkpoint settings, but the shared
    // checker contract reserves the unified checkpoint API surface until the
    // sequential/parallel setup paths converge on one checkpoint hook.
    #[allow(dead_code)] // Reserved API surface: sequential/parallel checkpoint convergence pending
    fn set_checkpoint(&mut self, dir: PathBuf, interval: Duration);
    fn set_progress_callback(&mut self, callback: ProgressCallback);
    /// Set fingerprint collision detection mode.
    /// Default implementation is a no-op (parallel checker does not yet support collision detection).
    fn set_collision_check_mode(&mut self, _mode: CollisionCheckMode) {}

    /// Apply all resource limits from a [`ResourceBudget`] in a single call.
    ///
    /// Only applies non-zero limits (zero = unlimited in the budget contract).
    /// `timeout_secs` is managed at the CLI/runner layer and is not applied here.
    #[allow(dead_code)]
    fn apply_budget(&mut self, budget: &ResourceBudget) {
        if budget.max_states > 0 {
            self.set_max_states(budget.max_states);
        }
        if budget.max_depth > 0 {
            self.set_max_depth(budget.max_depth);
        }
        if budget.memory_bytes > 0 {
            self.set_memory_limit(budget.memory_bytes);
        }
        if budget.disk_bytes > 0 {
            self.set_disk_limit(budget.disk_bytes);
        }
    }
}

impl<'a> CheckerConfigurable for ModelChecker<'a> {
    fn register_file_path(&mut self, file_id: FileId, path: PathBuf) {
        self.register_file_path(file_id, path);
    }
    fn register_inline_next(&mut self, resolved: &ResolvedSpec) -> Result<(), CheckError> {
        self.register_inline_next(resolved)
    }
    fn set_deadlock_check(&mut self, check: bool) {
        self.set_deadlock_check(check);
    }
    fn set_stuttering_allowed(&mut self, allowed: bool) {
        self.set_stuttering_allowed(allowed);
    }
    fn set_continue_on_error(&mut self, continue_on_error: bool) {
        self.set_continue_on_error(continue_on_error);
    }
    fn set_store_states(&mut self, store: bool) {
        self.set_store_states(store);
    }
    fn set_auto_create_trace_file(&mut self, auto_create: bool) {
        self.set_auto_create_trace_file(auto_create);
    }
    fn set_fairness(&mut self, fairness: Vec<FairnessConstraint>) {
        self.set_fairness(fairness);
    }
    fn set_fingerprint_storage(&mut self, storage: Arc<dyn FingerprintSet>) {
        self.set_fingerprint_storage(storage);
    }
    fn set_max_states(&mut self, limit: usize) {
        self.set_max_states(limit);
    }
    fn set_max_depth(&mut self, limit: usize) {
        self.set_max_depth(limit);
    }
    fn set_memory_limit(&mut self, limit_bytes: usize) {
        self.set_memory_limit(limit_bytes);
    }
    fn set_disk_limit(&mut self, limit_bytes: usize) {
        self.set_disk_limit(limit_bytes);
    }
    fn set_checkpoint(&mut self, dir: PathBuf, interval: Duration) {
        self.set_checkpoint(dir, interval);
    }
    fn set_progress_callback(&mut self, callback: ProgressCallback) {
        self.set_progress_callback(callback);
    }
    fn set_collision_check_mode(&mut self, mode: CollisionCheckMode) {
        self.set_collision_check_mode(mode);
    }
}

impl CheckerConfigurable for ParallelChecker {
    fn register_file_path(&mut self, file_id: FileId, path: PathBuf) {
        self.register_file_path(file_id, path);
    }
    fn register_inline_next(&mut self, resolved: &ResolvedSpec) -> Result<(), CheckError> {
        self.register_inline_next(resolved)
    }
    fn set_deadlock_check(&mut self, check: bool) {
        self.set_deadlock_check(check);
    }
    fn set_stuttering_allowed(&mut self, allowed: bool) {
        self.set_stuttering_allowed(allowed);
    }
    fn set_continue_on_error(&mut self, continue_on_error: bool) {
        self.set_continue_on_error(continue_on_error);
    }
    fn set_store_states(&mut self, store: bool) {
        self.set_store_states(store);
    }
    fn set_auto_create_trace_file(&mut self, auto_create: bool) {
        self.set_auto_create_trace_file(auto_create);
    }
    fn set_fairness(&mut self, fairness: Vec<FairnessConstraint>) {
        self.set_fairness(fairness);
    }
    fn set_fingerprint_storage(&mut self, storage: Arc<dyn FingerprintSet>) {
        self.set_fingerprint_storage(storage);
    }
    fn set_max_states(&mut self, limit: usize) {
        self.set_max_states(limit);
    }
    fn set_max_depth(&mut self, limit: usize) {
        self.set_max_depth(limit);
    }
    fn set_memory_limit(&mut self, limit_bytes: usize) {
        self.set_memory_limit(limit_bytes);
    }
    fn set_disk_limit(&mut self, limit_bytes: usize) {
        self.set_disk_limit(limit_bytes);
    }
    fn set_checkpoint(&mut self, dir: PathBuf, interval: Duration) {
        self.set_checkpoint(dir, interval);
    }
    fn set_progress_callback(&mut self, callback: ProgressCallback) {
        self.set_progress_callback(callback);
    }
}
