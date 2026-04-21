// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Setup and configuration methods for `AdaptiveChecker`.
//!
//! Extracted from `adaptive.rs` for decomposition (#3538).
//! Contains constructors (`new`, `new_with_extends`) and all `set_*` mutators.

use super::*;

impl AdaptiveChecker {
    /// Create a new adaptive model checker
    pub fn new(module: &Module, config: &Config) -> Self {
        Self::new_with_extends(module, &[], config)
    }

    /// Create a new adaptive model checker with additional loaded modules.
    ///
    /// Despite the historical name, `extended_modules` is **not** "EXTENDS-only".
    /// It must be a *loaded-module superset* for the whole run:
    ///
    /// - Include every non-stdlib module that may be referenced, via `EXTENDS` or `INSTANCE`
    ///   (including transitive and nested instance dependencies).
    /// - Put the modules that contribute to the **unqualified** operator namespace first, in a
    ///   TLC-shaped deterministic order (the `EXTENDS` closure and standalone `INSTANCE` imports).
    ///   Remaining loaded modules may follow in any deterministic order.
    ///
    /// Missing referenced non-stdlib modules are treated as a setup error.
    pub fn new_with_extends(
        module: &Module,
        extended_modules: &[&Module],
        config: &Config,
    ) -> Self {
        // Use shared lightweight setup pipeline (Part of #810).
        let lightweight = crate::checker_setup::setup_lightweight(module, extended_modules);
        let setup_error = lightweight.setup_error;
        let has_variables = lightweight.has_variables;
        #[allow(clippy::redundant_closure_for_method_calls)]
        let available_cores = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        let extended_modules: Vec<Arc<Module>> = extended_modules
            .iter()
            .map(|m| Arc::new((*m).clone()))
            .collect();
        AdaptiveChecker {
            setup_error,
            module: Arc::new(module.clone()),
            extended_modules,
            config: config.clone(),
            has_variables,
            inline_next: None,
            file_id_to_path: FxHashMap::default(),
            check_deadlock: config.check_deadlock,
            stuttering_allowed: true,
            max_states: None,
            max_depth: None,
            memory_limit: None,
            disk_limit: None,
            progress_callback: None,
            available_cores,
            fairness: Vec::new(),
            collect_coverage: false,
            coverage_guided: false,
            coverage_mix_ratio: 8,
            store_full_states: false,
            auto_create_trace_file: true,
            fingerprint_storage: None,
            continue_on_error: false,
            collision_check_mode: crate::collision_detection::CollisionCheckMode::None,
        }
    }

    /// Provide a source path for a given FileId to enable TLC-style line/col location rendering.
    ///
    /// If a path is not registered (or cannot be read), location rendering falls back to byte
    /// offsets (e.g. "bytes 0-0 of module M").
    pub fn register_file_path(&mut self, file_id: FileId, path: PathBuf) {
        self.file_id_to_path.entry(file_id).or_insert(path);
    }

    /// Enable or disable deadlock checking
    pub fn set_deadlock_check(&mut self, check: bool) {
        self.check_deadlock = check;
    }

    /// Set whether stuttering transitions are allowed.
    ///
    /// Forwarded to spawned `ModelChecker` instances for liveness checking.
    pub fn set_stuttering_allowed(&mut self, allowed: bool) {
        self.stuttering_allowed = allowed;
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
        self.continue_on_error = continue_on_error;
    }

    /// Enable or disable storing full states for trace reconstruction.
    ///
    /// When `store` is false (no-trace mode), counterexample traces will be unavailable.
    /// This can significantly reduce memory usage for large state spaces.
    pub fn set_store_states(&mut self, store: bool) {
        self.store_full_states = store;
    }

    /// Set whether to auto-create a temp trace file for fingerprint-only mode.
    ///
    /// When true (default): Creates a temporary trace file automatically if
    /// `store_full_states` is false and no explicit trace file is set.
    ///
    /// When false (--no-trace mode): No trace file is created, traces are
    /// completely unavailable for maximum memory efficiency.
    pub fn set_auto_create_trace_file(&mut self, auto_create: bool) {
        self.auto_create_trace_file = auto_create;
    }

    /// Set the fingerprint storage backend.
    ///
    /// This allows using memory-mapped storage for large state spaces that
    /// exceed available RAM. Must be called before `check()`.
    ///
    /// Only used when `store_full_states` is false (no-trace mode).
    /// When `store_full_states` is true, full states are stored regardless of this setting.
    pub fn set_fingerprint_storage(&mut self, storage: Arc<dyn FingerprintSet>) {
        self.fingerprint_storage = Some(storage);
    }

    /// Set fairness constraints from SPECIFICATION formula
    ///
    /// These constraints are passed to the sequential ModelChecker for liveness checking.
    pub fn set_fairness(&mut self, fairness: Vec<FairnessConstraint>) {
        self.fairness = fairness;
    }

    /// Register an inline NEXT expression from a ResolvedSpec.
    ///
    /// When the SPECIFICATION formula contains an inline NEXT expression like
    /// `Init /\ [][\E n \in Node: Next(n)]_vars`, the `resolved.next_node` contains
    /// the CST node for the expression. The resolved spec is stored and forwarded
    /// to the ModelChecker/ParallelChecker created in `check()`.
    ///
    /// Call this after creating the checker if `resolved.next_node` is Some.
    pub fn register_inline_next(&mut self, resolved: &ResolvedSpec) -> Result<(), CheckError> {
        if resolved.next_node.is_none() {
            return Ok(()); // No inline NEXT, nothing to do
        }

        self.inline_next = Some(resolved.clone());

        Ok(())
    }

    /// Enable or disable per-action coverage statistics collection.
    ///
    /// Coverage collection is implemented in the sequential `ModelChecker`, so enabling this
    /// forces the adaptive strategy to choose `Strategy::Sequential`.
    pub fn set_collect_coverage(&mut self, collect: bool) {
        self.collect_coverage = collect;
    }

    /// Enable or disable coverage-guided exploration.
    ///
    /// Coverage-guided exploration uses a hybrid priority frontier that directs
    /// exploration toward states exercising rare/uncovered actions. Forces
    /// sequential strategy. Implicitly enables coverage collection.
    pub fn set_coverage_guided(&mut self, enabled: bool, mix_ratio: usize) {
        self.coverage_guided = enabled;
        self.coverage_mix_ratio = mix_ratio;
        if enabled {
            self.collect_coverage = true;
        }
    }

    /// Set maximum number of states to explore
    pub fn set_max_states(&mut self, limit: usize) {
        self.max_states = Some(limit);
    }

    /// Set maximum BFS depth to explore
    pub fn set_max_depth(&mut self, limit: usize) {
        self.max_depth = Some(limit);
    }

    /// Part of #2751: Set memory limit for threshold-triggered stop.
    pub fn set_memory_limit(&mut self, limit_bytes: usize) {
        self.memory_limit = Some(limit_bytes);
    }

    /// Part of #3282: Set disk usage limit in bytes.
    pub fn set_disk_limit(&mut self, limit_bytes: usize) {
        self.disk_limit = Some(limit_bytes);
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

    /// Set a progress callback
    pub fn set_progress_callback(&mut self, callback: ProgressCallback) {
        self.progress_callback = Some(callback);
    }

    /// Set fingerprint collision detection mode.
    pub fn set_collision_check_mode(
        &mut self,
        mode: crate::collision_detection::CollisionCheckMode,
    ) {
        self.collision_check_mode = mode;
    }
}
