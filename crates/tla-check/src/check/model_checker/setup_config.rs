// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Configuration mutator and accessor surface for `ModelChecker`.
//!
//! Extracted from `setup.rs` as part of #2359 Phase 2 decomposition.
//! Contains setter/getter methods that configure exploration parameters,
//! storage backends, callbacks, and checkpoint settings.

use super::debug::skip_liveness;
use super::{
    Arc, Duration, FairnessConstraint, Fingerprint, FingerprintSet, InitProgressCallback,
    ModelChecker, PathBuf, ProgressCallback, TraceFile, TraceLocationsStorage,
};

/// Derive internal memory limit from env var or from the RSS limit.
///
/// Checks `TLA2_INTERNAL_MEMORY_LIMIT` first (bytes, 0 = disabled).
/// Falls back to 75% of the RSS `limit_bytes`, reserving 25% for code
/// segments, stack, eval context, and allocator overhead.
///
/// Part of #4080: OOM safety — hard internal memory cap.
pub(crate) fn internal_memory_limit_from_env_or_default(rss_limit_bytes: usize) -> usize {
    static CACHED: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    let env_override = *CACHED.get_or_init(|| {
        std::env::var("TLA2_INTERNAL_MEMORY_LIMIT")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
    });
    match env_override {
        Some(0) => 0, // Explicitly disabled
        Some(v) => v,
        None => {
            // 75% of the RSS limit reserved for internal stores.
            (rss_limit_bytes as f64 * 0.75) as usize
        }
    }
}

impl<'a> ModelChecker<'a> {
    fn refresh_liveness_successor_storage(&mut self, storage: &dyn FingerprintSet) {
        if !self.liveness_cache.cache_for_liveness {
            return;
        }

        let use_disk = match crate::liveness::debug::disk_successors_override() {
            Some(force) => force,
            None => {
                crate::liveness::debug::use_disk_successors()
                    || storage.prefers_disk_successor_graph()
            }
        };

        if use_disk == self.liveness_cache.successors.is_disk() {
            return;
        }

        self.liveness_cache.successors = if use_disk {
            crate::storage::SuccessorGraph::disk().expect("disk successor graph creation failed")
        } else {
            crate::storage::SuccessorGraph::default()
        };
    }

    /// Set fairness constraints from a resolved SPECIFICATION formula
    ///
    /// These constraints will be conjoined with negated liveness properties
    /// during liveness checking.
    pub fn set_fairness(&mut self, fairness: Vec<FairnessConstraint>) {
        self.liveness_cache.fairness = fairness;
    }

    /// Enable or disable per-action coverage statistics collection.
    ///
    /// When enabled, the model checker will enumerate each detected action separately and
    /// record per-action transition counts and "enabled in states" counts.
    pub fn set_collect_coverage(&mut self, collect: bool) {
        self.coverage.collect = collect;
    }

    /// Enable or disable coverage-guided exploration.
    ///
    /// When enabled, the BFS frontier uses a hybrid priority queue that
    /// directs exploration toward states exercising rare/uncovered actions.
    /// Implicitly enables coverage collection.
    ///
    /// `mix_ratio` controls how often to pick from the priority queue:
    /// - 8 (default): every 8th state is coverage-guided
    /// - 1: always prefer coverage-guided (pure priority)
    /// - 0: never use priority (pure BFS)
    pub fn set_coverage_guided(&mut self, enabled: bool, mix_ratio: usize) {
        self.coverage.coverage_guided = enabled;
        self.coverage.mix_ratio = mix_ratio;
        if enabled {
            // Coverage-guided implies coverage collection
            self.coverage.collect = true;
            self.coverage.tracker = Some(crate::coverage::guided::CoverageTracker::new());
        }
    }

    /// Check if coverage-guided exploration is enabled.
    #[allow(dead_code)] // Coverage-guided not yet wired into BFS loop
    pub(crate) fn is_coverage_guided(&self) -> bool {
        self.coverage.coverage_guided
    }

    /// Get a mutable reference to the coverage tracker (if active).
    #[allow(dead_code)] // Coverage-guided not yet wired into BFS loop
    pub(in crate::check::model_checker) fn coverage_tracker_mut(
        &mut self,
    ) -> Option<&mut crate::coverage::guided::CoverageTracker> {
        self.coverage.tracker.as_mut()
    }

    pub(in crate::check::model_checker) fn update_coverage_totals(&mut self) {
        if let Some(ref mut coverage) = self.stats.coverage {
            coverage.total_states = self.stats.states_found;
            coverage.total_transitions = self.stats.transitions;
        }
    }

    /// Enable or disable deadlock checking
    pub fn set_deadlock_check(&mut self, check: bool) {
        self.exploration.check_deadlock = check;
    }

    /// Set whether stuttering transitions are allowed.
    ///
    /// When `true` (`[A]_v` form), the liveness checker adds self-loop edges to the
    /// behavior graph so that infinite stuttering is visible to SCC analysis. This is
    /// required for correct liveness verdicts on specs using `[][Next]_vars`.
    ///
    /// When `false` (`<<A>>_v` form), no stuttering self-loops are injected.
    pub fn set_stuttering_allowed(&mut self, allowed: bool) {
        self.exploration.stuttering_allowed = allowed;
    }

    /// Enable continue-on-error mode (like TLC's -continue flag)
    ///
    /// When enabled, exploration continues after finding an invariant or property
    /// violation. The first violation is recorded but exploration continues until
    /// the full state space is exhausted (or limits are reached). Final stats
    /// include all reachable states.
    ///
    /// This is useful for:
    /// - Getting stable state counts for error specs (comparable with TLC -continue)
    /// - Finding all reachable states even when some violate invariants
    pub fn set_continue_on_error(&mut self, continue_on_error: bool) {
        self.exploration.continue_on_error = continue_on_error;
    }

    /// Record an invariant violation, returning whether to stop exploration.
    ///
    /// In continue_on_error mode, this records the first violation and returns `false`
    /// to signal that exploration should continue. Otherwise returns `true` to stop.
    ///
    /// Note: This only applies to invariant violations, NOT deadlocks. Deadlocks always
    /// stop immediately, matching TLC's `-continue` behavior which only continues after
    /// invariant violations.
    pub(in crate::check::model_checker) fn record_invariant_violation(
        &mut self,
        invariant: String,
        state_fp: Fingerprint,
    ) -> bool {
        if self.exploration.continue_on_error {
            // Record first violation but continue exploring (TLC -continue mode)
            if self.exploration.first_violation.is_none()
                && self.exploration.first_action_property_violation.is_none()
            {
                self.exploration.first_violation = Some((invariant, state_fp));
            }
            false // Continue exploring
        } else {
            true // Stop immediately
        }
    }

    /// Record an action-level PROPERTY violation.
    pub(in crate::check::model_checker) fn record_action_property_violation(
        &mut self,
        property: String,
        state_fp: Fingerprint,
    ) -> bool {
        if self.exploration.continue_on_error {
            if self.exploration.first_violation.is_none()
                && self.exploration.first_action_property_violation.is_none()
            {
                self.exploration.first_action_property_violation = Some((property, state_fp));
            }
            false
        } else {
            true
        }
    }

    /// Set maximum number of states to explore
    ///
    /// When this limit is reached, model checking stops with `CheckResult::LimitReached`.
    /// This is useful for unbounded specifications that would otherwise run indefinitely.
    pub fn set_max_states(&mut self, limit: usize) {
        self.exploration.max_states = Some(limit);
    }

    /// Set maximum BFS depth to explore
    ///
    /// When this limit is reached, model checking stops with `CheckResult::LimitReached`.
    /// Depth 0 = initial states, depth 1 = first successors, etc.
    pub fn set_max_depth(&mut self, limit: usize) {
        self.exploration.max_depth = Some(limit);
    }

    /// Part of #2751 Phase 2+3: Set a memory limit for threshold-triggered stop.
    ///
    /// When RSS reaches 85% of `limit_bytes`, exploration stops gracefully
    /// with a `LimitReached { limit_type: Memory }` result.
    ///
    /// Also auto-derives an internal memory hard cap at 75% of the limit
    /// unless an explicit internal limit was already set.
    pub fn set_memory_limit(&mut self, limit_bytes: usize) {
        self.exploration.memory_policy = Some(crate::memory::MemoryPolicy::new(limit_bytes));
        // Part of #4080: auto-derive internal memory cap from RSS limit.
        if self.exploration.internal_memory_limit.is_none() {
            self.exploration.internal_memory_limit =
                Some(internal_memory_limit_from_env_or_default(limit_bytes));
        }
    }

    /// Part of #4080: Set a hard cap on estimated internal memory (bytes).
    ///
    /// When the sum of all in-memory stores (FP set + seen + depths + queue)
    /// exceeds this limit, BFS stops gracefully. 0 = disabled.
    pub fn set_internal_memory_limit(&mut self, limit_bytes: usize) {
        self.exploration.internal_memory_limit = if limit_bytes > 0 {
            Some(limit_bytes)
        } else {
            None
        };
    }

    /// Part of #3282: Set a disk usage limit in bytes.
    ///
    /// When disk-backed storage (DiskFingerprintSet) would exceed this limit,
    /// exploration stops gracefully with `LimitReached { limit_type: Disk }`.
    pub fn set_disk_limit(&mut self, limit_bytes: usize) {
        self.exploration.disk_limit_bytes = Some(limit_bytes);
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

    /// Set a shared verdict for portfolio racing.
    ///
    /// When set, the BFS worker loop checks the verdict every 4096 states
    /// and exits early if another lane has resolved. After BFS completes,
    /// the result is published to the verdict so other lanes can exit.
    ///
    /// Part of #3717.
    pub fn set_portfolio_verdict(&mut self, verdict: Arc<crate::shared_verdict::SharedVerdict>) {
        self.portfolio_verdict = Some(verdict);
    }

    /// Set cooperative state for fused BFS+symbolic mode (CDEMC).
    ///
    /// When set, the BFS worker loop:
    /// - Checks `invariants_proved` periodically and skips invariant evaluation
    /// - Samples frontier states at level boundaries for symbolic seeding
    /// - Checks the cooperative verdict for early exit
    ///
    /// Part of #3767, Epic #3762.
    #[cfg(feature = "z4")]
    pub fn set_cooperative_state(
        &mut self,
        state: Arc<crate::cooperative_state::SharedCooperativeState>,
    ) {
        self.cooperative = Some(state);
    }

    /// Set a progress callback to receive periodic updates during model checking
    ///
    /// The callback is called approximately every `interval` states (default: 1000).
    /// This is useful for long-running model checks to show progress to users.
    pub fn set_progress_callback(&mut self, callback: ProgressCallback) {
        self.hooks.progress_callback = Some(callback);
    }

    /// Set an init progress callback to receive a one-shot update after Init completes.
    ///
    /// This is useful for tool integrations that want to reflect the transition from
    /// initial-state enumeration to reachability exploration.
    pub fn set_init_progress_callback(&mut self, callback: InitProgressCallback) {
        self.hooks.init_progress_callback = Some(callback);
    }

    /// Sync TLC config to the evaluation context for TLCGet("config") support
    ///
    /// The `mode` parameter specifies the exploration mode:
    /// - "bfs" for exhaustive model checking
    /// - "generate" for simulation/random behavior generation
    pub(in crate::check::model_checker) fn sync_tlc_config(&mut self, mode: &str) {
        use crate::eval::TlcConfig;
        let config = TlcConfig::new(
            Arc::from(mode),
            self.exploration.max_depth.map_or(-1, |d| d as i64),
            self.exploration.check_deadlock,
        );
        self.ctx.set_tlc_config(config);
    }

    /// Set the collision detection mode for fingerprint-based state storage.
    ///
    /// - `None`: Zero overhead (default). Only theoretical collision probability
    ///   is reported.
    /// - `Sampling { interval }`: Store one full state per N admitted states and
    ///   verify fingerprint uniqueness. Catches collisions with probability 1/N.
    /// - `Full`: Store all states and verify every fingerprint is unique.
    ///   Catches all collisions but doubles memory usage.
    ///
    /// Must be called before `check()`. Results are reported in `CheckStats`.
    pub fn set_collision_check_mode(
        &mut self,
        mode: crate::collision_detection::CollisionCheckMode,
    ) {
        if mode.is_active() {
            self.collision_detector =
                Some(crate::collision_detection::CollisionDetector::new(mode));
        } else {
            self.collision_detector = None;
        }
    }

    /// Set how often progress is reported (in number of states)
    ///
    /// Default is 1000 states. Setting to 0 disables progress reporting.
    #[cfg(test)]
    pub(crate) fn set_progress_interval(&mut self, interval: usize) {
        self.hooks.progress_interval = interval;
    }

    /// Set whether to store full states for trace reconstruction
    ///
    /// When `store` is true (legacy mode):
    /// - Full states are stored in memory (42x more memory than fingerprint-only)
    /// - Faster trace reconstruction (no replay needed)
    /// - Also enables eager full-state access for liveness replay/diagnostics
    ///
    /// When `store` is false (default, #88):
    /// - Only fingerprints are stored, not full states
    /// - Significantly reduces memory usage for large state spaces
    /// - Counterexample traces reconstructed via temp trace file (unless disabled)
    /// - Liveness still works via BFS-time caching and replay (#3175)
    ///
    /// Default is false (fingerprint-only for 42x memory reduction).
    pub fn set_store_states(&mut self, store: bool) {
        self.state_storage.store_full_states = store;
        // Part of #3709: on-the-fly liveness skips the cached successor graph
        // entirely and regenerates successors lazily during product exploration.
        self.liveness_cache.cache_for_liveness = !self.config.properties.is_empty()
            && !skip_liveness()
            && !self.config.liveness_execution.uses_on_the_fly();
        self.refresh_liveness_mode();
    }

    /// Mark the trace as degraded (test-only helper).
    #[cfg(test)]
    pub fn set_trace_degraded(&mut self, degraded: bool) {
        self.trace.trace_degraded = degraded;
    }

    /// Set whether to auto-create a temp trace file for fingerprint-only mode
    ///
    /// When true (default): Creates a temporary trace file automatically if
    /// `store_full_states` is false and no explicit trace file is set.
    ///
    /// When false (--no-trace mode): No trace file is created, traces are
    /// completely unavailable for maximum memory efficiency.
    pub fn set_auto_create_trace_file(&mut self, auto_create: bool) {
        self.trace.auto_create_trace_file = auto_create;
    }

    /// Set the fingerprint storage backend.
    ///
    /// This allows using memory-mapped storage for large state spaces that
    /// exceed available RAM. Must be called before `check()`.
    ///
    /// Only used when `store_full_states` is false (no-trace mode).
    /// When `store_full_states` is true, full states are stored in a HashMap
    /// regardless of this setting.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use std::sync::Arc;
    /// use tla_check::{Config, FingerprintSet, FingerprintStorage, ModelChecker};
    /// use tla_core::{lower, parse_to_syntax_tree, FileId};
    ///
    /// let src = "---- MODULE Counter ----\n\
    /// VARIABLE x\n\
    /// Init == x = 0\n\
    /// Next == x' = x + 1 /\\ x < 1\n\
    /// ====";
    /// let tree = parse_to_syntax_tree(src);
    /// let lowered = lower(FileId(0), &tree);
    /// let module = lowered.module.expect("valid module");
    ///
    /// let config = Config::parse("INIT Init\nNEXT Next\n").expect("valid config");
    /// let mut checker = ModelChecker::new(&module, &config);
    /// checker.set_store_states(false); // Enable no-trace mode
    ///
    /// let storage = FingerprintStorage::mmap(10_000_000, None).expect("mmap storage");
    /// checker.set_fingerprint_storage(Arc::new(storage) as Arc<dyn FingerprintSet>);
    /// let _result = checker.check();
    /// ```
    pub fn set_fingerprint_storage(&mut self, storage: Arc<dyn FingerprintSet>) {
        self.refresh_liveness_successor_storage(storage.as_ref());
        self.state_storage.seen_fps = storage;
    }

    /// Enable disk-based trace storage for large state space exploration.
    ///
    /// When enabled, the model checker writes (predecessor_loc, fingerprint) pairs
    /// to a disk file instead of keeping full states in memory. This significantly
    /// reduces memory usage while still enabling counterexample trace reconstruction.
    ///
    /// When a violation is found, the trace is reconstructed by:
    /// 1. Walking backward through the trace file to collect fingerprints
    /// 2. Replaying from the initial state, generating successors and matching
    ///    by fingerprint until the error state is reached
    ///
    /// # Arguments
    ///
    /// * `trace_file` - The trace file to use for storage
    ///
    /// # Notes
    ///
    /// - Trace file mode is incompatible with `store_full_states = true` (the two
    ///   approaches are mutually exclusive)
    /// - Trace reconstruction is slower than in-memory trace storage because states
    ///   must be regenerated from fingerprints
    /// - Part of #3175: Liveness checking now works with trace file mode
    pub fn set_trace_file(&mut self, trace_file: TraceFile) {
        self.trace.trace_file = Some(trace_file);
        // Trace file mode implies we don't store full states in memory
        self.state_storage.store_full_states = false;
        // Part of #3175: keep liveness active even with trace file.
        // BFS-time inline evaluation doesn't need stored full states.
        self.liveness_cache.cache_for_liveness =
            !self.config.properties.is_empty() && !skip_liveness();
    }

    /// Set the trace location storage for fingerprint-to-offset mapping.
    ///
    /// By default, trace locations are stored in memory. For large state spaces,
    /// use `TraceLocationsStorage::mmap()` to scale beyond available RAM.
    ///
    /// # Arguments
    ///
    /// * `storage` - The trace location storage to use
    pub fn set_trace_locations_storage(&mut self, storage: TraceLocationsStorage) {
        self.trace.trace_locs = storage;
    }

    /// Enable checkpoint saving during model checking.
    ///
    /// Checkpoints are saved periodically to the specified directory, allowing
    /// interrupted model checking runs to be resumed.
    ///
    /// # Arguments
    ///
    /// * `dir` - Directory to save checkpoint files
    /// * `interval` - Interval between checkpoints
    pub fn set_checkpoint(&mut self, dir: PathBuf, interval: Duration) {
        self.checkpoint.dir = Some(dir);
        self.checkpoint.interval = interval;
    }

    /// Set the spec and config paths for checkpoint metadata.
    ///
    /// These paths are stored in checkpoint metadata to help verify on resume
    /// that the checkpoint matches the current spec/config. SHA-256 content
    /// hashes are computed eagerly so that file modifications between
    /// checkpoint save and resume are detected even when the path is unchanged.
    pub fn set_checkpoint_paths(&mut self, spec_path: Option<String>, config_path: Option<String>) {
        if let Some(spec_path) = spec_path.as_deref() {
            let path = std::path::Path::new(spec_path);
            self.ctx
                .set_input_base_dir(path.parent().map(std::path::Path::to_path_buf));
            self.checkpoint.spec_hash = crate::checkpoint::compute_file_hash(path);
        }
        if let Some(config_path) = config_path.as_deref() {
            self.checkpoint.config_hash =
                crate::checkpoint::compute_file_hash(std::path::Path::new(config_path));
        }
        self.checkpoint.spec_path = spec_path;
        self.checkpoint.config_path = config_path;
    }
}
