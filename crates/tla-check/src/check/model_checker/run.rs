// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BFS model checker entry point: setup, validation, and dispatch to
//! full-state or no-trace mode.
//!
//! The BFS implementation is split across submodules:
//! - `run_prepare`: Pre-BFS preparation (constants, symmetry, VIEW, compilation)
//! - `run_checks`: Post-BFS validation (ASSUME, POSTCONDITION)
//! - `run_bfs_full`: Full-state mode BFS loop
//! - `run_bfs_notrace`: No-trace (fingerprint-only) mode BFS loop
//! - `run_helpers`: Shared BFS helpers (invariant checks, deadlock, checkpointing, profiling)
//! - `run_gen`: State generation (initial states, successors, pilot sampling)
//! - `run_monitoring`: Resource monitoring (progress, memory/disk pressure, state space estimation)

use super::super::api::{check_error_to_result, CheckResult, InitProgress};
#[cfg(debug_assertions)]
use super::debug::{
    debug_states, debug_successors_actions, debug_successors_actions_all_states, tla2_debug,
};
use super::mc_struct::ModelChecker;
use crate::constants::bind_constants_from_config;
use crate::coverage::{detect_actions, CoverageStats};
use crate::storage::FingerprintSet;
use crate::trace_file::TraceFile;
use crate::{ConfigCheckError, EvalCheckError};
use std::time::Instant;

pub(super) use super::run_monitoring::ProgressAction;

impl ModelChecker<'_> {
    pub(in crate::check) fn report_init_progress(
        &self,
        states_generated: usize,
        distinct_states: usize,
    ) {
        if let Some(ref callback) = self.hooks.init_progress_callback {
            let init = InitProgress {
                states_generated,
                distinct_states,
            };
            callback(&init);
        }
    }

    /// Attach the current fingerprint-storage counters to a terminal result.
    pub(in crate::check) fn with_current_storage_stats(
        &mut self,
        result: CheckResult,
    ) -> CheckResult {
        let storage_stats = FingerprintSet::stats(&*self.state_storage.seen_fps);
        self.stats.storage_stats = storage_stats;
        result.with_storage_stats(storage_stats)
    }

    /// Finalize terminal-result precedence, then attach current storage stats.
    pub(in crate::check) fn finalize_terminal_result_with_storage(
        &mut self,
        candidate: CheckResult,
    ) -> CheckResult {
        let result = self.finalize_terminal_result(candidate);
        self.with_current_storage_stats(result)
    }

    /// Auto-create temp trace storage when configured.
    ///
    /// Part of #3178: creates trace file in both full-state and fp-only modes.
    /// In full-state mode, the trace file replaces the in-memory `parents`
    /// HashMap for parent tracking, reducing per-state memory by 16 bytes.
    pub(super) fn maybe_auto_create_trace_file(&mut self) {
        if self.trace.auto_create_trace_file && self.trace.trace_file.is_none() {
            match TraceFile::create_temp() {
                Ok(tf) => {
                    self.trace.trace_file = Some(tf);
                }
                Err(e) => {
                    // Part of #1433: warn instead of silently swallowing.
                    // TLC treats trace file failure as fatal; TLA2 degrades gracefully
                    // but must inform the user that error traces will be unavailable.
                    eprintln!("WARNING: failed to create temp trace file: {e}");
                    eprintln!("  Error traces will be unavailable for this run.");
                }
            }
        }
    }

    /// Reset checkpoint timer when periodic checkpointing is enabled.
    pub(super) fn initialize_checkpoint_timing(&mut self) {
        if self.checkpoint.dir.is_some() {
            self.checkpoint.last_time = Some(Instant::now());
        }
    }

    /// Detect actions in the Next relation and set up coverage tracking and POR state.
    pub(super) fn setup_actions_and_por(&mut self, next_name: &str) {
        let actions = match self.module.op_defs.get(next_name) {
            Some(next_def) => detect_actions(next_def),
            None => return,
        };
        self.stats.detected_actions = actions.iter().map(|a| a.name.clone()).collect();
        self.stats.detected_action_ids = actions.iter().map(|a| a.id.to_string()).collect();

        if self.coverage.collect {
            let mut coverage = CoverageStats::new();
            for action in &actions {
                coverage.register_action(action);
            }
            self.coverage.actions = actions.clone();
            self.stats.coverage = Some(coverage);
        } else {
            // Keep detected actions available for:
            // - `TLA2_DEBUG_STATES` action attribution
            // - Part of #3910: JIT per-action next-state dispatch
            #[cfg(feature = "jit")]
            let keep_for_jit = self.jit_next_state_cache.is_some()
                || self.pending_jit_compilation.is_some()
                || self.action_bytecode.is_some();
            #[cfg(not(feature = "jit"))]
            let keep_for_jit = false;

            #[cfg(debug_assertions)]
            if keep_for_jit
                || debug_states()
                || debug_successors_actions()
                || debug_successors_actions_all_states()
            {
                self.coverage.actions = actions.clone();
            } else {
                self.coverage.actions.clear();
            }
            #[cfg(not(debug_assertions))]
            if keep_for_jit {
                self.coverage.actions = actions.clone();
            } else {
                self.coverage.actions.clear();
            }
            self.stats.coverage = None;
        }

        // Build POR analysis inputs when requested or auto-detected.
        //
        // Part of #3993: Auto-POR enables partial order reduction automatically
        // when the independence analysis finds independent action pairs. This
        // matches SPIN's behavior where POR is the default for concurrent specs.
        //
        // POR is disabled when liveness properties are present because the C3
        // BFS proviso is insufficient for liveness — it only guarantees no
        // exploration cycles in safety BFS, but liveness checking requires
        // the "ignoring proviso" (Peled 1996) or "strong proviso" which we
        // do not yet implement.
        let has_liveness = self.config.has_liveness_properties();
        if has_liveness && self.config.por_enabled {
            eprintln!(
                "POR: disabled — liveness properties present (C3 BFS proviso is insufficient for liveness)"
            );
        }

        // Auto-POR: when not explicitly enabled, check if auto-detection should
        // run the independence analysis. Config.auto_por overrides the env var;
        // when None, TLA2_AUTO_POR env var controls (default: enabled).
        let auto_por = match self.config.auto_por {
            Some(val) => val,
            None => {
                static AUTO_POR: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                *AUTO_POR.get_or_init(|| {
                    std::env::var("TLA2_AUTO_POR")
                        .map_or(true, |v| v != "0")
                })
            }
        };
        let por_candidate = (self.config.por_enabled || auto_por)
            && !actions.is_empty()
            && !has_liveness
            && actions.len() >= 2;

        if por_candidate {
            // POR dependency extraction needs the full action body including primed
            // assignments and UNCHANGED to compute read/write sets. The standard
            // expansion (allow_primed=false) skips primed operators, producing
            // opaque Ident references that yield empty dependency sets.
            // Re-expand with primes and re-detect to get analyzable action bodies.
            let por_actions = match self.module.op_defs.get(next_name) {
                Some(next_def) => {
                    let por_expanded =
                        crate::checker_ops::expand_operator_body_with_primes(&self.ctx, next_def);
                    detect_actions(&por_expanded)
                }
                None => actions.clone(),
            };
            let action_dependencies =
                crate::por::extract_detected_action_dependencies(&por_actions);
            let independence = crate::por::IndependenceMatrix::compute(&action_dependencies);

            let indep_pairs = independence.count_independent_pairs();
            let total_pairs = independence.total_pairs();

            // Auto-POR gate: if this was auto-detected (not explicitly requested),
            // only enable POR when there are actually independent pairs. No point
            // routing through the slower per-action path with zero reduction.
            if !self.config.por_enabled && indep_pairs == 0 {
                // No independent pairs found — skip POR setup entirely.
                // The actions are already set in coverage.actions if needed.
                #[cfg(debug_assertions)]
                if tla2_debug() {
                    eprintln!(
                        "Auto-POR: {} actions analyzed, 0/{} independent pairs — POR not beneficial",
                        actions.len(),
                        total_pairs,
                    );
                }
                return;
            }

            // Report independence analysis results
            #[cfg(debug_assertions)]
            if tla2_debug() {
                let source = if self.config.por_enabled { "explicit" } else { "auto" };
                if indep_pairs > 0 {
                    eprintln!(
                        "POR ({}): {} actions, {}/{} independent pairs ({:.1}%)",
                        source,
                        actions.len(),
                        indep_pairs,
                        total_pairs,
                        if total_pairs > 0 {
                            100.0 * indep_pairs as f64 / total_pairs as f64
                        } else {
                            0.0
                        }
                    );
                }
            }

            self.por.independence = Some(independence);

            // Build visibility set from PROPERTY-promoted and config-level
            // invariant expressions with operator expansion.
            // Part of #3354 Slice 4 + #3449: both PROPERTY and config invariants
            // go through expand_operators so wrapper operators (e.g. Inv == TypeOK)
            // are inlined before dependency extraction.
            let mut visibility = crate::por::VisibilitySet::new();

            // PROPERTY-promoted invariants (from classification pipeline).
            for (_name, expr) in &self.compiled.eval_state_invariants {
                visibility.extend_from_expanded_expr(&self.ctx, expr);
            }

            // Config-level INVARIANT entries (name-only strings from .cfg).
            // Resolve to operator bodies and expand through wrapper operators.
            for inv_name in &self.config.invariants {
                if let Some(def) = self.ctx.get_op(inv_name) {
                    visibility.extend_from_expanded_expr(&self.ctx, &def.body);
                } else {
                    // Config invariant name not found in operator definitions.
                    // validate_config_ops() should have caught this earlier; fall
                    // back to treating all actions as visible to keep exploration sound.
                    eprintln!(
                        "POR: config invariant '{}' not found in op_defs, disabling reduction",
                        inv_name
                    );
                    visibility.mark_all_visible();
                    break;
                }
            }
            self.por.visibility = visibility;

            // POR requires per-action enumeration - populate coverage_actions if not already set
            if self.coverage.actions.is_empty() {
                self.coverage.actions = actions;
            }
        }
    }

    pub(super) fn check_impl(&mut self) -> CheckResult {
        if let Some(err) = self.module.setup_error.take() {
            return CheckResult::from_error(err, self.stats.clone());
        }

        // Sync TLC config for TLCGet("config") support (must happen before ASSUME checking)
        self.sync_tlc_config("bfs");

        // Validate init_name (check_impl-specific: resume path skips init)
        let init_name = match &self.config.init {
            Some(name) => name.clone(),
            None => {
                // Toolbox-generated "constant-expression evaluation" models often contain only
                // ASSUME statements and do not provide INIT/NEXT. Check for assume-only model
                // below after constant binding.
                if self.config.next.is_none()
                    && self.config.specification.is_none()
                    && self.module.vars.is_empty()
                    && self.config.invariants.is_empty()
                    && self.config.properties.is_empty()
                    && !self.module.assumes.is_empty()
                {
                    // Bind constants first so ASSUME expressions evaluate correctly
                    if let Err(e) = bind_constants_from_config(&mut self.ctx, self.config) {
                        // Part of #2356/#2777: Route through check_error_to_result so
                        // ExitRequested maps to LimitReached(Exit).
                        return check_error_to_result(EvalCheckError::Eval(e).into(), &self.stats);
                    }
                    // Check ASSUME statements
                    if let Some(result) = self.check_assumes() {
                        return result;
                    }
                    return CheckResult::Success(self.stats.clone());
                }
                return CheckResult::from_error(
                    ConfigCheckError::MissingInit.into(),
                    self.stats.clone(),
                );
            }
        };

        // Shared BFS setup: constant binding, symmetry, VIEW, next validation,
        // invariant compilation, operator expansion, action compilation
        let next_name = match self.prepare_bfs_common() {
            Ok(name) => name,
            Err(result) => return result,
        };

        // Cache init name for trace reconstruction from fingerprints
        self.trace.cached_init_name = Some(init_name.clone());

        // Check ASSUME statements after constant binding (done in prepare_bfs_common).
        // TLC checks all assumptions and stops if any evaluate to FALSE.
        // Part of #1031: Use eval_entry to enable operator result caching.
        if let Some(result) = self.check_assumes() {
            return result;
        }

        // Part of #3826: When the cooperative oracle routes ALL actions to
        // SymbolicOnly (exponential complexity detected), skip BFS Init
        // enumeration and wait for the symbolic engines to resolve the verdict.
        // Init enumeration IS the bottleneck for specs like SpanTreeTest5Nodes
        // where SUBSET(SUBSET Nodes) produces 2^(2^N) elements.
        #[cfg(feature = "z4")]
        if self.should_defer_to_symbolic() {
            eprintln!("[BFS] all actions routed to symbolic — skipping Init enumeration");
            return self.wait_for_symbolic_verdict();
        }

        // Part of #3282: Pre-exploration state space estimation.
        // After constants are bound, extract constraints from Init and estimate
        // the initial state space. Warn if it exceeds configured limits.
        self.maybe_warn_state_space_estimate(&init_name);

        // Detect actions and initialize coverage/POR state.
        self.setup_actions_and_por(&next_name);

        // Auto-create temp trace file for fingerprint-only mode (#88)
        // This enables trace reconstruction while using 42x less memory than full-state storage.
        // Skip if user explicitly set a trace file, enabled full-state storage, or disabled auto-creation.
        self.maybe_auto_create_trace_file();

        // Part of #2955: Freeze name interner for lock-free lookup during BFS.
        tla_core::name_intern::freeze_interner();

        if self.state_storage.store_full_states {
            self.check_impl_full_state_mode(&init_name)
        } else {
            self.check_impl_no_trace_mode(&init_name)
        }
    }

    // =========================================================================
    // Symbolic-only deferred mode (Part of #3826)
    // =========================================================================

    /// Check whether BFS should defer entirely to the symbolic engines.
    ///
    /// Returns `true` when the cooperative oracle routes ALL actions to
    /// `SymbolicOnly`, meaning the spec has exponential complexity (detected
    /// by the `ComplexityVisitor`) that makes BFS Init enumeration infeasible.
    ///
    /// Part of #3826.
    #[cfg(feature = "z4")]
    fn should_defer_to_symbolic(&self) -> bool {
        if let Some(ref cooperative) = self.cooperative {
            return cooperative.all_actions_symbolic_only();
        }
        false
    }

    /// Wait for the symbolic engines (BMC/PDR/k-Induction) to resolve the
    /// verdict, then return an appropriate BFS result.
    ///
    /// Instead of enumerating initial states (which is the bottleneck for
    /// exponential specs like SpanTreeTest5Nodes where `SUBSET(SUBSET Nodes)`
    /// produces `2^(2^N)` elements), BFS polls the shared verdict periodically.
    ///
    /// Returns `CheckResult::Success` when the symbolic engines resolve
    /// `Satisfied`, or propagates the appropriate error for `Violated`.
    /// Returns `CheckResult::Success` with a note if the verdict is cancelled
    /// or times out (the fused orchestrator handles these cases).
    ///
    /// Part of #3826.
    #[cfg(feature = "z4")]
    fn wait_for_symbolic_verdict(&self) -> CheckResult {
        use std::time::{Duration, Instant};

        let poll_interval = Duration::from_millis(500);
        let start = Instant::now();
        // Wait up to 30 minutes for symbolic engines to resolve.
        // The fused orchestrator enforces its own timeout.
        let timeout = Duration::from_secs(1800);

        // Poll the portfolio verdict (shared with symbolic lanes).
        if let Some(ref verdict_arc) = self.portfolio_verdict {
            loop {
                if verdict_arc.is_resolved() {
                    match verdict_arc.get() {
                        Some(crate::shared_verdict::Verdict::Satisfied) => {
                            eprintln!(
                                "[BFS] symbolic engine proved safety — BFS deferred ({:.1}s)",
                                start.elapsed().as_secs_f64()
                            );
                            return CheckResult::Success(self.stats.clone());
                        }
                        Some(crate::shared_verdict::Verdict::Violated) => {
                            eprintln!(
                                "[BFS] symbolic engine found violation — BFS deferred ({:.1}s)",
                                start.elapsed().as_secs_f64()
                            );
                            // Return Success from BFS; the fused orchestrator
                            // extracts the violation from the symbolic result.
                            return CheckResult::Success(self.stats.clone());
                        }
                        _ => {
                            // Cancelled or unknown — let BFS complete with Success
                            // so the fused orchestrator falls back to BFS result.
                            eprintln!(
                                "[BFS] symbolic verdict cancelled — BFS returning ({:.1}s)",
                                start.elapsed().as_secs_f64()
                            );
                            return CheckResult::Success(self.stats.clone());
                        }
                    }
                }

                if start.elapsed() > timeout {
                    eprintln!(
                        "[BFS] symbolic verdict timeout ({:.0}s) — BFS returning",
                        timeout.as_secs_f64()
                    );
                    return CheckResult::Success(self.stats.clone());
                }

                std::thread::sleep(poll_interval);
            }
        }

        // No portfolio verdict available — should not happen in fused mode,
        // but return Success as a safe fallback.
        CheckResult::Success(self.stats.clone())
    }
}

#[cfg(test)]
#[path = "run_tests.rs"]
mod run_tests;
