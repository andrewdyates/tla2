// Licensed under the Apache License, Version 2.0

// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel checker orchestration and lifecycle.

use super::parallel_profiling;
#[cfg(debug_assertions)]
use super::tla2_debug;
use super::{
    check_and_warn_capacity, check_invariants_array_state, check_state_constraints_array,
    timing_enabled, use_handle_state, use_shared_queue, FairnessConstraint, FxBuildHasher,
    ParallelChecker, ParallelCollisionDiagnostics, ParentLog, WorkBarrier, WorkerResult,
    WorkerStats, CAPACITY_NORMAL,
};
use super::{
    run_worker_shared_queue, run_worker_unified, BfsWorkItem, WorkerModelConfig, WorkerSharedState,
};
use crate::arena::BulkStateStorage;
use crate::check::{
    check_error_to_result, compute_uses_trace, CheckError, CheckResult, CheckStats, LimitType,
    Progress, ProgressCallback, Trace,
};
use crate::config::Config;
use crate::constants::bind_constants_from_config;
use crate::coverage::detect_actions;
use crate::enumerate::{
    enumerate_constraints_to_bulk, enumerate_states_from_constraint_branches,
    extract_conjunction_remainder, extract_init_constraints, find_unconstrained_vars,
    print_enum_profile_stats,
};
use crate::eval::{EvalCtx, TlcConfig};
use crate::intern::HandleState;
use crate::periodic_liveness::PeriodicLivenessState;
use crate::state::{states_to_trace_value, ArrayState, Fingerprint, State};
use crate::storage::factory::{
    default_parallel_fpset_capacity, FingerprintSetFactory, StorageConfig, StorageMode,
};
use crate::storage::{FingerprintSet, InsertOutcome};
use crate::var_index::VarRegistry;
use crate::Value;
use crossbeam_channel::{bounded, Receiver, Sender};
use crossbeam_deque::{Injector, Stealer, Worker};
use dashmap::DashMap;
use rustc_hash::FxHashMap;
#[cfg(test)]
use rustc_hash::FxHashSet;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::thread;
use std::time::{Duration, Instant};
#[cfg(test)]
use tla_core::ast::Expr;
use tla_core::ast::{Module, OperatorDef};
#[cfg(test)]
use tla_core::span::Spanned;

mod check_lifecycle;
#[cfg(test)]
mod checker_tests;
mod config_env;
mod construction;
mod finalize;
#[cfg(test)]
mod finalize_tests;
mod init_processing;
mod init_states;
mod liveness;
mod liveness_execution;
mod liveness_graph;
mod liveness_on_the_fly;
mod liveness_safety;
mod module_setup;
mod periodic_maintenance;
mod prepare;
mod seeding;
pub(super) mod terminal_outcome;
mod types;

use config_env::parallel_fpset_mode;
use config_env::parallel_readonly_value_caches_enabled;
use types::{panic_payload_message, CheckPreparation, CheckRuntime, InitialStates};

use crate::checker_setup::{setup_checker_modules, CheckerSetup, SetupOptions};
use crate::ConfigCheckError;
use init_processing::{bulk_len_as_u32, SeedingCtx};

impl ParallelChecker {
    /// Enable or disable deadlock checking
    pub fn set_deadlock_check(&mut self, check: bool) {
        self.check_deadlock = check;
    }

    /// Set fairness constraints from the SPECIFICATION formula.
    ///
    /// Part of #2740: These are conjoined with the negated property during
    /// post-BFS liveness checking, matching the sequential checker's behavior.
    pub fn set_fairness(&mut self, fairness: Vec<FairnessConstraint>) {
        self.fairness = fairness;
    }

    /// Part of #2762: Set whether stuttering transitions are allowed.
    /// `[A]_v` → true, `<<A>>_v` → false.
    pub fn set_stuttering_allowed(&mut self, allowed: bool) {
        self.stuttering_allowed = allowed;
    }

    /// Part of #2772: Set whether to auto-create a temp trace file for fingerprint-only mode.
    ///
    /// When true (default): Creates a temporary trace file automatically if
    /// `store_full_states` is false and no explicit trace file is set.
    ///
    /// When false (--no-trace mode): No trace file is created, traces are
    /// completely unavailable for maximum memory efficiency.
    ///
    /// Note: The parallel checker does not currently support trace files, but
    /// plumbing this setting prevents silent config loss from AdaptiveChecker.
    pub fn set_auto_create_trace_file(&mut self, auto_create: bool) {
        self.auto_create_trace_file = auto_create;
    }

    /// Part of #2772: Provide a source path for a given FileId to enable TLC-style
    /// line/col location rendering.
    ///
    /// If a path is not registered (or cannot be read), location rendering falls back
    /// to byte offsets (e.g. "bytes 0-0 of module M").
    pub fn register_file_path(&mut self, file_id: tla_core::FileId, path: std::path::PathBuf) {
        if file_id == tla_core::FileId(0) {
            self.input_base_dir = path.parent().map(std::path::Path::to_path_buf);
        }
        self.file_id_to_path.entry(file_id).or_insert(path);
    }

    /// Part of #2749: Set checkpoint directory and interval.
    ///
    /// When set, the parallel checker periodically suspends all workers and
    /// saves a checkpoint to disk. The checkpoint can be used to resume
    /// exploration after interruption.
    pub fn set_checkpoint(&mut self, dir: PathBuf, interval: Duration) {
        self.checkpoint_dir = Some(dir);
        self.checkpoint_interval = interval;
    }

    /// Part of #2749: Set spec and config paths for checkpoint identity validation.
    ///
    /// On resume, these paths are checked against the checkpoint metadata to
    /// ensure the checkpoint matches the current spec/config.
    pub fn set_checkpoint_paths(&mut self, spec: Option<String>, config: Option<String>) {
        self.checkpoint_spec_path = spec;
        self.checkpoint_config_path = config;
    }

    /// Part of #2751 Phase 2+3: Set a memory limit for threshold-triggered
    /// checkpoint and graceful stop.
    ///
    /// Also auto-derives an internal memory hard cap at 75% of the limit
    /// unless an explicit internal limit was already set.
    pub fn set_memory_limit(&mut self, limit_bytes: usize) {
        self.memory_policy = Some(crate::memory::MemoryPolicy::new(limit_bytes));
        // Part of #4080: auto-derive internal memory cap from RSS limit.
        if self.internal_memory_limit.is_none() {
            let env_or_default = crate::check::model_checker::setup::setup_config::internal_memory_limit_from_env_or_default(limit_bytes);
            self.internal_memory_limit = if env_or_default > 0 {
                Some(env_or_default)
            } else {
                None
            };
        }
    }

    /// Part of #4080: Set a hard cap on estimated internal memory (bytes).
    /// 0 = disabled.
    pub fn set_internal_memory_limit(&mut self, limit_bytes: usize) {
        self.internal_memory_limit = if limit_bytes > 0 {
            Some(limit_bytes)
        } else {
            None
        };
    }

    /// Part of #3282: Set a disk usage limit in bytes.
    ///
    /// When disk-backed storage would exceed this limit, exploration stops
    /// gracefully with `LimitReached { limit_type: Disk }`.
    pub fn set_disk_limit(&mut self, limit_bytes: usize) {
        self.disk_limit_bytes = Some(limit_bytes);
    }

    /// Enable or disable continue-on-error mode (TLC -continue semantics).
    ///
    /// When enabled, exploration continues after finding an invariant violation.
    /// The first violation is recorded, but the checker continues exploring
    /// until the full state space is exhausted (or limits are reached).
    /// Final stats reflect the complete reachable state count, making counts
    /// stable and comparable with TLC -continue.
    ///
    /// Violating states (including initial states) are still expanded; the violation is recorded
    /// and reported after exploration completes to match TLC `-continue`.
    pub fn set_continue_on_error(&mut self, enable: bool) {
        self.continue_on_error = enable;
    }

    /// Enable or disable storing full states for trace reconstruction.
    ///
    /// When `store` is false (no-trace mode), only fingerprints are stored and
    /// counterexample traces will be unavailable.
    ///
    /// Part of #1139: If invariants reference Trace, store_full_states
    /// is automatically enabled regardless of the requested setting.
    pub fn set_store_states(&mut self, store: bool) {
        // Part of #1139: Auto-enable store_full_states when Trace is used.
        // Trace operator requires full state reconstruction.
        if self.uses_trace && !store {
            // Silently override user request - full state storage is required for Trace
            debug_eprintln!(
                tla2_debug(),
                "[DEBUG] ParallelChecker: auto-enabling store_full_states (Trace requires full state storage)"
            );
            self.store_full_states = true;
        } else {
            self.store_full_states = store;
        }
    }

    /// Set the fingerprint storage backend.
    ///
    /// This allows using memory-mapped storage for large state spaces that
    /// exceed available RAM. Must be called before `check()`.
    ///
    /// Only used when `store_full_states` is false (no-trace mode).
    /// When `store_full_states` is true, full states are stored in a DashMap
    /// regardless of this setting.
    pub fn set_fingerprint_storage(&mut self, storage: Arc<dyn FingerprintSet>) {
        self.seen_fps = storage;
    }

    /// Set fingerprint collision detection mode.
    ///
    /// Collision detection is not yet implemented for the parallel checker.
    /// This method is a no-op; the mode is accepted but ignored.
    pub fn set_collision_check_mode(
        &mut self,
        _mode: crate::collision_detection::CollisionCheckMode,
    ) {
        // Parallel collision detection is future work.
    }

    /// Register an inline NEXT expression from a ResolvedSpec.
    ///
    /// Delegates CST lowering and OperatorDef construction to the shared
    /// `checker_ops::lower_inline_next`, then registers the result in op_defs
    /// and recomputes Trace usage (Part of #1121).
    pub fn register_inline_next(
        &mut self,
        resolved: &crate::check::ResolvedSpec,
    ) -> Result<(), crate::check::CheckError> {
        let op_def = match crate::checker_ops::lower_inline_next(
            resolved.next_node.as_ref(),
            &self.var_registry,
        ) {
            None => return Ok(()),
            Some(result) => result?,
        };

        // Register the operator in our definitions
        self.op_defs
            .insert(crate::check::INLINE_NEXT_NAME.to_string(), op_def);

        // Part of #1121: Inline NEXT is registered after checker construction.
        // Recompute Trace usage so detector covers the actual evaluated NEXT body.
        self.uses_trace = match compute_uses_trace(&self.config, &self.op_defs) {
            Ok(val) => val,
            Err(e) => {
                if self.setup_error.is_none() {
                    self.setup_error = Some(e);
                }
                false
            }
        };

        // Keep state-storage policy consistent with `set_store_states`.
        if self.uses_trace && !self.store_full_states {
            debug_eprintln!(
                tla2_debug(),
                "[DEBUG] ParallelChecker: auto-enabling store_full_states after inline NEXT registration (Trace requires full state storage)"
            );
            self.store_full_states = true;
        }

        Ok(())
    }

    /// Get the number of states found (works in both modes)
    pub(crate) fn states_count(&self) -> usize {
        if self.store_full_states {
            self.seen.len()
        } else {
            self.seen_fps.len()
        }
    }

    /// Estimate the total bytes consumed by in-memory stores.
    ///
    /// Part of #4080: OOM safety — parallel internal memory accounting.
    pub(crate) fn estimate_internal_memory_bytes(&self) -> usize {
        self.memory_breakdown().total_bytes
    }

    /// Produce a structured breakdown of internal memory usage.
    ///
    /// Part of #4080: OOM safety — structured memory accounting.
    pub(crate) fn memory_breakdown(&self) -> crate::memory::MemoryBreakdown {
        let fp_bytes = FingerprintSet::stats(&*self.seen_fps).memory_bytes;

        let seen_bytes = if self.store_full_states {
            let num_vars = self.vars.len();
            let value_size = num_vars.saturating_mul(64);
            let count = self.seen.len();
            let estimated_capacity = count.saturating_mul(2);
            let entry_size = 8usize.saturating_add(value_size);
            crate::memory::estimate_dashmap_bytes_raw(estimated_capacity, entry_size)
        } else {
            0
        };

        let depths_bytes = if self.checkpoint_dir.is_some() {
            let count = self.depths.len();
            let estimated_capacity = count.saturating_mul(2);
            crate::memory::estimate_dashmap_bytes_raw(
                estimated_capacity,
                std::mem::size_of::<crate::state::Fingerprint>() + std::mem::size_of::<usize>(),
            )
        } else {
            0
        };

        let parent_log_bytes = self.parent_log.estimate_memory_bytes();

        // Part of #4080: estimate liveness cache memory.
        let liveness_bytes = {
            let succ_bytes = self
                .successors
                .as_ref()
                .map(|dm| {
                    let count = dm.len();
                    let estimated_capacity = count.saturating_mul(2);
                    let entry_size = std::mem::size_of::<crate::state::Fingerprint>()
                        .saturating_add(std::mem::size_of::<Vec<crate::state::Fingerprint>>());
                    crate::memory::estimate_dashmap_bytes_raw(estimated_capacity, entry_size)
                })
                .unwrap_or(0);

            let witness_bytes = self
                .successor_witnesses
                .as_ref()
                .map(|dm| {
                    let count = dm.len();
                    let estimated_capacity = count.saturating_mul(2);
                    let entry_size = std::mem::size_of::<crate::state::Fingerprint>()
                        .saturating_add(std::mem::size_of::<
                            Vec<(crate::state::Fingerprint, crate::state::ArrayState)>,
                        >());
                    crate::memory::estimate_dashmap_bytes_raw(estimated_capacity, entry_size)
                })
                .unwrap_or(0);

            let init_bytes = {
                let count = self.liveness_init_states.len();
                if count > 0 {
                    let estimated_capacity = count.saturating_mul(2);
                    let entry_size = std::mem::size_of::<crate::state::Fingerprint>()
                        .saturating_add(std::mem::size_of::<crate::state::ArrayState>());
                    crate::memory::estimate_dashmap_bytes_raw(estimated_capacity, entry_size)
                } else {
                    0
                }
            };

            succ_bytes
                .saturating_add(witness_bytes)
                .saturating_add(init_bytes)
        };

        crate::memory::MemoryBreakdown::new(fp_bytes, seen_bytes, depths_bytes, 0, parent_log_bytes)
            .with_liveness(liveness_bytes)
    }

    /// Set maximum number of states to explore
    ///
    /// When this limit is reached, model checking stops with `CheckResult::LimitReached`.
    /// This is useful for unbounded specifications that would otherwise run indefinitely.
    pub fn set_max_states(&mut self, limit: usize) {
        self.max_states_limit = Some(limit);
    }

    /// Set maximum BFS depth to explore
    ///
    /// When this limit is reached, model checking stops with `CheckResult::LimitReached`.
    /// Depth 0 = initial states, depth 1 = first successors, etc.
    pub fn set_max_depth(&mut self, limit: usize) {
        self.max_depth_limit = Some(limit);
    }

    /// Apply all resource limits from a [`ResourceBudget`] in a single call.
    ///
    /// Only applies non-zero limits (zero = unlimited in the budget contract).
    /// `timeout_secs` is managed at the CLI/runner layer and is not applied here.
    pub fn apply_budget(&mut self, budget: &crate::resource_budget::ResourceBudget) {
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

    /// Set a progress callback to receive periodic updates during model checking
    ///
    /// The callback is called approximately every `interval_ms` milliseconds (default: 1000ms).
    /// This is useful for long-running model checks to show progress to users.
    pub fn set_progress_callback(&mut self, callback: ProgressCallback) {
        self.progress_callback = Some(Arc::new(callback));
    }

    /// Run the parallel model checker.
    ///
    /// # Panics
    ///
    /// Panics if called more than once on the same instance. `ParallelChecker`
    /// has one-shot semantics: run-state (seen maps, stop_flag, counters,
    /// first_violation) is not reset between calls. Create a new checker for
    /// each model-check run. Fix for #1851.
    pub fn check(&self) -> CheckResult {
        if let Some(result) =
            crate::check::runtime_config_validation_result(&self.config, &CheckStats::default())
        {
            return result;
        }
        assert!(
            !self.has_run.swap(true, Ordering::SeqCst),
            "ParallelChecker::check() called more than once. \
             ParallelChecker is one-shot: create a new instance for each run. \
             Re-use would observe stale stop_flag, counters, and seen maps (#1851)."
        );

        self.run_check_inner()
    }

    /// Inner BFS execution: prepare, seed, spawn workers, finalize.
    ///
    /// Shared between `check()` (fresh run) and `check_with_resume()` (re-exploration
    /// after checkpoint restore). The one-shot guard (`has_run`) is the caller's
    /// responsibility.
    pub(crate) fn run_check_inner(&self) -> CheckResult {
        crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);
        let _subset_profile_guard = crate::enumerate::subset_profile::RunGuard::begin();
        crate::guard_error_stats::reset();
        struct GuardErrorStatsFlush;
        impl Drop for GuardErrorStatsFlush {
            fn drop(&mut self) {
                crate::guard_error_stats::emit_warning_and_reset();
            }
        }
        let _guard_error_stats_flush = GuardErrorStatsFlush;

        let mut prep = match self.prepare_check() {
            Ok(prep) => prep,
            Err(result) => return result,
        };

        // Part of #2955: Freeze the name interner before spawning BFS workers.
        // This snapshots the lookup table so that intern_name()/lookup_name_id()
        // bypass the global RwLock entirely during parallel evaluation.
        tla_core::name_intern::freeze_interner();

        // Part of #3285, Part of #3334: Freeze the value interners and set cache mode
        // via RAII guard. Drop handles teardown on both normal and early-return paths.
        let cache_mode = match parallel_readonly_value_caches_enabled() {
            Ok(true) => tla_value::SharedValueCacheMode::Readonly,
            Ok(false) => tla_value::SharedValueCacheMode::Writable,
            Err(e) => {
                return CheckResult::from_error(e, CheckStats::default());
            }
        };
        let _value_intern_guard = tla_value::ParallelValueInternRunGuard::new(cache_mode);

        let detected_actions = std::mem::take(&mut prep.detected_actions);
        let detected_action_ids = std::mem::take(&mut prep.detected_action_ids);
        let promoted_properties = std::mem::take(&mut prep.promoted_properties);
        let state_property_violation_names =
            std::mem::take(&mut prep.state_property_violation_names);
        let promoted_property_invariants = std::mem::take(&mut prep.promoted_property_invariants);
        // Part of #2676: Store on self so checkpoint resume can access it.
        let _ = self
            .promoted_property_invariants
            .set(promoted_property_invariants.clone());

        // Part of #3910: Initialize tiered JIT state for parallel promotion tracking.
        // Workers atomically increment per-action eval counters; the progress thread
        // periodically checks for tier promotions.
        if crate::check::debug::jit_enabled() {
            let action_count = detected_actions.len().max(1);
            let action_labels: Vec<Option<String>> = if detected_actions.len() > 1 {
                detected_actions
                    .iter()
                    .map(|name| Some(name.clone()))
                    .collect()
            } else {
                vec![None; action_count]
            };
            let tier = Arc::new(crate::parallel::tier_state::SharedTierState::new(
                action_count,
                action_labels,
            ));

            // Wave 11a (Part of #4267): the JIT next-state cache wiring
            // previously threaded a compiled action bytecode cache into
            // `SharedTierState::set_jit_next_state_cache`. That API was
            // removed alongside the Cranelift deletion (Epic #4251);
            // workers fall through to the tree-walk interpreter.

            let _ = self.tier_state.set(tier);
        }

        let runtime = match self.seed_and_spawn_workers(&mut prep) {
            Ok(rt) => rt,
            Err(result) => {
                // Guard drop unfreezes interners and disables read-only cache mode.
                return result;
            }
        };

        let result = self.finalize_check(
            runtime,
            detected_actions,
            detected_action_ids,
            &mut prep.ctx,
            promoted_properties,
            state_property_violation_names,
        );

        // Guard drop unfreezes interners now that all workers are done
        // and finalize_check() has consumed the remaining results.
        // This MUST be in run_check_inner(), not in finalize_check(), because
        // unit tests call finalize_check() directly in parallel — mutating
        // the process-global FROZEN_SNAPSHOT mutex there causes poisoning
        // when the interner_cleanup test runs concurrently.

        result
    }
}

/// Run parallel model checking on a module
///
/// # Arguments
/// * `module` - The TLA+ module to check
/// * `config` - Model checking configuration
/// * `num_workers` - Number of worker threads (0 = auto-detect based on CPU count)
///
/// # Returns
/// The result of model checking (success, violation, deadlock, or error)
pub fn check_module_parallel(module: &Module, config: &Config, num_workers: usize) -> CheckResult {
    if let Some(result) = crate::check::config_validation_result(config, &CheckStats::default()) {
        return result;
    }
    let checker = ParallelChecker::new(module, config, num_workers);
    checker.check()
}
