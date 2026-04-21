// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adaptive Model Checker - Automatically selects sequential or parallel execution
//!
//! This module implements an adaptive approach to model checking that:
//! 1. Runs a pilot phase to sample the spec's characteristics
//! 2. Estimates the total state space size based on branching factor
//! 3. Automatically selects sequential or parallel execution based on heuristics
//!
//! # Heuristics
//!
//! Re: #3202 (Category C scaling gate, 2026-03-14). Current evidence:
//!
//! MCKVSSafetySmall (3.4M states): TLA2 barely scales in parallel — ~1.4x
//! at 8 workers vs TLC's ~3.5x. Single-worker TLA2 is ~0.65x TLC.
//!
//! MCBoulanger (7.9M states): TLA2 1-worker is ~1.1x TLC, but parallel
//! mode degrades severely at 2+ workers (timeout/crash on some runs).
//!
//! Selector thresholds kept unchanged pending parallel bottleneck
//! investigation. See reports/perf/issue-3202-category-c-parallel-scaling-current.md
//!
//! The adaptive checker uses initial state count and sampled branching factor
//! to estimate spec size and select the optimal strategy.

// Submodules extracted from this file for decomposition (#2745).
// Using #[path] to keep files as siblings in src/ without modifying lib.rs.
#[path = "checker_config.rs"]
mod checker_config;
#[path = "adaptive_setup.rs"]
mod setup;
#[path = "strategy.rs"]
mod strategy;

// Re-export public types so `adaptive::{Strategy, PilotAnalysis}` still resolves
// (lib.rs re-exports from adaptive).
pub use strategy::{PilotAnalysis, Strategy};

use crate::check::{
    check_error_to_result, CheckResult, CheckStats, ModelChecker, ProgressCallback, ResolvedSpec,
};
use crate::config::Config;
use crate::eval::set_random_seed;
use crate::parallel::ParallelChecker;
use crate::spec_formula::FairnessConstraint;
use crate::storage::factory::{FingerprintSetFactory, StorageConfig, StorageMode};
use crate::storage::FingerprintSet;
use crate::CheckError;
use crate::ConfigCheckError;
use checker_config::CheckerConfigurable;
use rustc_hash::FxHashMap;
use std::path::PathBuf;
use std::sync::Arc;
use strategy::{estimate_state_space, select_strategy, PILOT_SAMPLE_SIZE};
use tla_core::ast::{Module, Unit};
use tla_core::FileId;

/// Adaptive model checker
pub struct AdaptiveChecker {
    /// Setup error detected during construction (e.g., missing referenced modules).
    setup_error: Option<CheckError>,
    /// The TLA+ module being checked
    module: Arc<Module>,
    /// Extended/instanced modules (kept separately for instance ops lookup)
    extended_modules: Vec<Arc<Module>>,
    /// Model checking configuration
    config: Config,
    /// Whether any module in scope declares state variables.
    /// Used for early detection of assume-only models and missing-variable errors.
    has_variables: bool,
    /// Cached resolved spec for inline NEXT registration (if any).
    inline_next: Option<ResolvedSpec>,
    /// Best-effort FileId -> source path mapping for TLC-style line/col locations.
    ///
    /// When absent for a given FileId (or unreadable), location rendering falls back to byte
    /// offsets (e.g. "bytes 0-0 of module M").
    file_id_to_path: FxHashMap<FileId, PathBuf>,
    /// Whether to check for deadlocks
    check_deadlock: bool,
    /// Whether stuttering transitions are allowed (`[A]_v` = true, `<<A>>_v` = false).
    /// Forwarded to spawned ModelChecker instances for liveness checking.
    stuttering_allowed: bool,
    /// Maximum states limit
    max_states: Option<usize>,
    /// Maximum depth limit
    max_depth: Option<usize>,
    /// Part of #2751: Memory limit in bytes
    memory_limit: Option<usize>,
    /// Part of #3282: Disk usage limit in bytes.
    disk_limit: Option<usize>,
    /// Progress callback
    progress_callback: Option<ProgressCallback>,
    /// Number of available CPU cores
    available_cores: usize,
    /// Fairness constraints from SPECIFICATION formula (for liveness checking)
    fairness: Vec<FairnessConstraint>,
    /// Whether to collect per-action coverage statistics (forces sequential strategy)
    collect_coverage: bool,
    /// Whether to use coverage-guided exploration (forces sequential strategy).
    coverage_guided: bool,
    /// Mix ratio for coverage-guided frontier (every N pops, one is priority-guided).
    coverage_mix_ratio: usize,
    /// Whether to store full states for trace reconstruction
    store_full_states: bool,
    /// Whether to auto-create temp trace file (for ModelChecker in fingerprint-only mode)
    auto_create_trace_file: bool,
    /// Optional fingerprint storage for no-trace mode (memory-mapped for large state spaces)
    fingerprint_storage: Option<Arc<dyn FingerprintSet>>,
    /// Continue exploring after invariant/property violations (like TLC's -continue flag)
    continue_on_error: bool,
    /// Fingerprint collision detection mode.
    collision_check_mode: crate::collision_detection::CollisionCheckMode,
}

impl AdaptiveChecker {
    /// Run pilot phase to analyze spec characteristics
    fn run_pilot(&mut self) -> Result<PilotAnalysis, CheckError> {
        if let Some(err) = self.setup_error.clone() {
            return Err(err);
        }

        // Toolbox-generated "constant-expression evaluation" models may contain only
        // ASSUME statements (sometimes with Print/PrintT side effects), but provide no
        // INIT/NEXT or SPECIFICATION and declare no state variables. Treat these as
        // successful assume-only checks and force sequential execution.
        if self.config.init.is_none()
            && self.config.next.is_none()
            && self.config.specification.is_none()
            && !self.has_variables
            && self.config.invariants.is_empty()
            && self.config.properties.is_empty()
            && self
                .module
                .units
                .iter()
                .any(|u| matches!(u.node, Unit::Assume(_)))
        {
            return Ok(PilotAnalysis {
                initial_states: 0,
                avg_branching_factor: 0.0,
                estimated_states: 0,
                strategy: Strategy::Sequential,
                states_sampled: 0,
            });
        }

        let init_name = self
            .config
            .init
            .clone()
            .ok_or(ConfigCheckError::MissingInit)?;
        let next_name = self
            .config
            .next
            .clone()
            .ok_or(ConfigCheckError::MissingNext)?;

        if !self.has_variables {
            return Err(ConfigCheckError::NoVariables.into());
        }

        let ext_refs: Vec<&Module> = self
            .extended_modules
            .iter()
            .map(std::convert::AsRef::as_ref)
            .collect();
        let mut pilot_checker =
            ModelChecker::new_with_extends(&self.module, &ext_refs, &self.config);
        for (file_id, path) in &self.file_id_to_path {
            pilot_checker.register_file_path(*file_id, path.clone());
        }
        if let Some(ref resolved) = self.inline_next {
            pilot_checker.register_inline_next(resolved)?;
        }
        let (num_initial, avg_branching_factor, states_sampled) = pilot_checker
            .pilot_sample_init_and_branching_factor(&init_name, &next_name, PILOT_SAMPLE_SIZE)?;

        if num_initial == 0 {
            return Err(ConfigCheckError::InitCannotEnumerate(
                "Init predicate has no solutions".to_string(),
            )
            .into());
        }

        // Estimate total states using geometric series approximation
        // For a BFS with branching factor b, after d levels: 1 + b + b^2 + ... + b^d
        // We estimate based on initial states and branching factor
        let estimated_states = estimate_state_space(num_initial, avg_branching_factor);

        // Select strategy based on estimate
        let strategy = select_strategy(estimated_states, self.available_cores);

        Ok(PilotAnalysis {
            initial_states: num_initial,
            avg_branching_factor,
            estimated_states,
            strategy,
            states_sampled,
        })
    }

    /// Run model checking with adaptive strategy selection
    pub fn check(&mut self) -> (CheckResult, Option<PilotAnalysis>) {
        if let Some(result) =
            crate::check::runtime_config_validation_result(&self.config, &CheckStats::default())
        {
            return (result, None);
        }
        if let Some(err) = self.setup_error.clone() {
            return (check_error_to_result(err, &CheckStats::default()), None);
        }

        crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);

        // Run pilot phase
        let mut analysis = match self.run_pilot() {
            Ok(a) => a,
            Err(e) => return (check_error_to_result(e, &CheckStats::default()), None),
        };

        // Part of #3194: TIR eval/parity is currently implemented only on the
        // sequential checker. Keep AdaptiveChecker on the supported path rather
        // than silently bypassing TIR by selecting ParallelChecker.
        // Part of #3285 measurement gate (2026-03-17): TIR leaf eval on parallel
        // is 2.6x SLOWER than compiled/split actions — TIR and CompiledAction are
        // mutually exclusive optimization layers, and split actions win for
        // multi-action specs. Keep forcing sequential for all TIR modes.
        if crate::tir_mode::tir_mode_requested() {
            analysis.strategy = Strategy::Sequential;
        }

        // Coverage collection is implemented in ModelChecker (sequential) only.
        if self.collect_coverage && analysis.strategy != Strategy::Sequential {
            analysis.strategy = Strategy::Sequential;
        }

        // Coverage-guided exploration requires sequential mode (priority decisions
        // depend on global coverage state).
        if self.coverage_guided && analysis.strategy != Strategy::Sequential {
            analysis.strategy = Strategy::Sequential;
        }

        // Trace invariants are implemented in ModelChecker (sequential) only.
        // ParallelChecker does not check them, so routing to parallel would
        // silently skip trace invariant evaluation — a correctness violation.
        // Part of #3752: Apalache Gap 4.
        if !self.config.trace_invariants.is_empty() && analysis.strategy != Strategy::Sequential {
            analysis.strategy = Strategy::Sequential;
        }

        // Auto-create factory-managed storage when the pilot estimates a large
        // state space and no explicit storage override was set. The factory's
        // Auto mode uses the capacity hint to select ShardedDisk when above
        // DISK_THRESHOLD, or Sharded/InMemory otherwise. (Part of #2568, Step 4)
        if self.fingerprint_storage.is_none() {
            let num_workers = match analysis.strategy {
                Strategy::Parallel(n) => n,
                Strategy::Sequential => 1,
            };
            if let Ok(storage) = FingerprintSetFactory::create(StorageConfig {
                mode: StorageMode::Auto { num_workers },
                capacity: Some(analysis.estimated_states),
                ..Default::default()
            }) {
                self.fingerprint_storage = Some(storage);
            }
        }

        // Set the RandomElement seed for reproducible behavior.
        // With fingerprint-based selection, this seed affects which elements are chosen
        // from sets, but the selection is always deterministic for a given seed.
        set_random_seed(12345);

        // Execute with selected strategy.
        // Clone module/config so the ModelChecker (which borrows them with lifetime
        // 'a) does not conflict with the &mut self borrow in apply_common_config.
        let module = Arc::clone(&self.module);
        let config = self.config.clone();
        let ext_refs: Vec<&Module> = self
            .extended_modules
            .iter()
            .map(std::convert::AsRef::as_ref)
            .collect();
        let result = match analysis.strategy {
            Strategy::Sequential => {
                let mut checker = ModelChecker::new_with_extends(&module, &ext_refs, &config);
                if let Err(e) = self.apply_common_config(&mut checker) {
                    return (
                        check_error_to_result(e, &CheckStats::default()),
                        Some(analysis),
                    );
                }
                checker.set_collect_coverage(self.collect_coverage);
                if self.coverage_guided {
                    checker.set_coverage_guided(true, self.coverage_mix_ratio);
                }
                checker.check()
            }
            Strategy::Parallel(workers) => {
                let mut checker =
                    ParallelChecker::new_with_extends(&module, &ext_refs, &config, workers);
                if let Err(e) = self.apply_common_config(&mut checker) {
                    return (
                        check_error_to_result(e, &CheckStats::default()),
                        Some(analysis),
                    );
                }
                checker.check()
            }
        };

        (result, Some(analysis))
    }

    /// Apply common configuration to a checker instance.
    ///
    /// This eliminates duplication between the sequential and parallel branches
    /// in `check()`. Any new setting that applies to both checker types should
    /// be added here (single code path).
    fn apply_common_config(
        &mut self,
        checker: &mut impl CheckerConfigurable,
    ) -> Result<(), CheckError> {
        for (file_id, path) in &self.file_id_to_path {
            checker.register_file_path(*file_id, path.clone());
        }
        if let Some(ref resolved) = self.inline_next {
            checker.register_inline_next(resolved)?;
        }
        checker.set_deadlock_check(self.check_deadlock);
        checker.set_stuttering_allowed(self.stuttering_allowed);
        checker.set_continue_on_error(self.continue_on_error);
        checker.set_store_states(self.store_full_states);
        checker.set_auto_create_trace_file(self.auto_create_trace_file);
        if !self.fairness.is_empty() {
            checker.set_fairness(self.fairness.clone());
        }
        if let Some(ref storage) = self.fingerprint_storage {
            checker.set_fingerprint_storage(Arc::clone(storage));
        }
        if let Some(limit) = self.max_states {
            checker.set_max_states(limit);
        }
        if let Some(limit) = self.max_depth {
            checker.set_max_depth(limit);
        }
        if let Some(limit) = self.memory_limit {
            checker.set_memory_limit(limit);
        }
        if let Some(limit) = self.disk_limit {
            checker.set_disk_limit(limit);
        }
        if let Some(callback) = self.progress_callback.take() {
            checker.set_progress_callback(callback);
        }
        checker.set_collision_check_mode(self.collision_check_mode);
        Ok(())
    }
}

/// Run adaptive model checking on a module
///
/// This is the recommended entry point for model checking. It automatically
/// selects the best execution strategy (sequential vs parallel) based on
/// the spec's characteristics.
///
/// # Returns
/// A tuple of (CheckResult, `Option<PilotAnalysis>`) where the analysis
/// contains details about the selected strategy.
pub fn check_module_adaptive(
    module: &Module,
    config: &Config,
) -> (CheckResult, Option<PilotAnalysis>) {
    let mut checker = AdaptiveChecker::new(module, config);
    checker.check()
}

#[cfg(test)]
#[path = "adaptive_tests.rs"]
mod tests;
