// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compiled BFS level loop integration for the model checker.
//!
//! When the compiled BFS step is available (all actions AND all invariants
//! JIT-compiled, fully-flat state layout), this module provides a level-based
//! BFS loop that processes entire frontiers from the contiguous `FlatBfsFrontier`
//! arena. Each parent state is fed through `CompiledBfsStep::step_flat()` which
//! performs action dispatch, inline fingerprinting, first-level dedup via
//! `AtomicFpSet`, and invariant checking in native Cranelift-compiled code.
//!
//! New successors are then passed through the model checker's global seen set
//! for second-level dedup and enqueued as `NoTraceQueueEntry::Flat` entries
//! into the frontier arena.
//!
//! # Design
//!
//! The compiled level loop replaces `run_bfs_loop` for specs that qualify:
//!
//! ```text
//! for each BFS level:
//!   get raw arena slice from FlatBfsFrontier
//!   for each parent in arena:
//!     compiled_step.step_flat(parent) -> FlatBfsStepOutput
//!     for each new successor:
//!       traditional_fingerprint via FlatBfsAdapter
//!       dedup against global seen set
//!       if new: enqueue as Flat entry + record trace
//!     handle invariant violations, deadlock
//!   advance read cursor (bulk consume)
//! ```
//!
//! Part of #3988: JIT V2 Phase 5 compiled BFS step.

use super::super::trace_invariant::TraceInvariantOutcome;
use super::super::{
    enumerate_successors, ArrayState, CheckResult, ModelChecker, OperatorDef, Trace,
};
use super::compiled_step_trait::CompiledBfsStepScratch;
use super::flat_frontier::FlatBfsFrontier;
use super::storage_modes::FingerprintOnlyStorage;
use crate::check::model_checker::frontier::BfsFrontier;
use crate::shared_verdict::Verdict;
use crate::state::Fingerprint;
use crate::storage::{InsertOutcome, TraceLocationStorage};
use crate::RuntimeCheckError;

/// Minimum number of parents between progress/memory pressure checks
/// during compiled BFS level processing. Matches the
/// `MEMORY_CHECK_INTERVAL` used by the standard BFS transport to ensure
/// OOM safety checks are not delayed until level-end.
///
/// Part of #4203.
const COMPILED_BFS_PROGRESS_INTERVAL: u64 = 4096;
const COMPILED_BFS_INTERPRETER_CROSSCHECK_ENV: &str = "TLA2_COMPILED_BFS_INTERPRETER_CROSSCHECK";

#[derive(Debug)]
struct CompiledBfsInterpreterActionSuccessors {
    action_idx: usize,
    action_name: String,
    successors: Vec<Vec<i64>>,
}

fn fused_successor_needs_pre_seen_lookup(
    regular_invariants_checked_by_backend: bool,
    regular_invariant_count: usize,
) -> bool {
    fused_successor_needs_rust_regular_invariant_check(
        regular_invariants_checked_by_backend,
        regular_invariant_count,
    )
}

fn fused_successor_needs_rust_regular_invariant_check(
    regular_invariants_checked_by_backend: bool,
    regular_invariant_count: usize,
) -> bool {
    !regular_invariants_checked_by_backend && regular_invariant_count > 0
}

/// Statistics from a compiled BFS level loop run.
#[derive(Debug, Default)]
pub(in crate::check::model_checker) struct CompiledBfsLoopStats {
    /// Wall-clock instant when compiled BFS execution starts, after cold JIT build/setup.
    pub(in crate::check::model_checker) execution_started_at: Option<std::time::Instant>,
    /// Total parents processed across all levels.
    pub(in crate::check::model_checker) parents_processed: u64,
    /// Total successors generated (before global dedup).
    pub(in crate::check::model_checker) successors_generated: u64,
    /// Total new successors after global dedup.
    pub(in crate::check::model_checker) successors_new: u64,
    /// BFS levels completed.
    pub(in crate::check::model_checker) levels_completed: usize,
    /// Per-parent compiled step outputs that borrowed reusable successor scratch.
    pub(in crate::check::model_checker) step_outputs_borrowed: u64,
    /// Per-parent compiled step outputs that owned a freshly materialized arena.
    pub(in crate::check::model_checker) step_outputs_owned: u64,
    /// Fused successors that still needed a pre-admission seen-set probe.
    pub(in crate::check::model_checker) fused_pre_seen_lookups: u64,
    /// Fused successors admitted through a single insert/test-and-set.
    pub(in crate::check::model_checker) fused_pre_seen_lookups_skipped: u64,
    /// Per-successor raw admission validations avoided after level-level checks.
    pub(in crate::check::model_checker) fused_admission_validations_elided: u64,
}

impl ModelChecker<'_> {
    fn compiled_bfs_interpreter_action_successors_for_parent(
        &mut self,
        parent_slice: &[i64],
        registry: &tla_core::VarRegistry,
    ) -> Result<Vec<CompiledBfsInterpreterActionSuccessors>, CheckResult> {
        let parent_state = self.try_reconstruct_state_from_flat(parent_slice, registry)?;
        let actions = self.coverage.actions.clone();
        if actions.is_empty() {
            return Ok(Vec::new());
        }

        let flat_layout = self
            .flat_bfs_adapter
            .as_ref()
            .map(|adapter| adapter.layout().clone())
            .or_else(|| self.flat_state_layout.clone())
            .ok_or_else(|| {
                CheckResult::from_error(
                    RuntimeCheckError::Internal(
                        "compiled BFS interpreter crosscheck missing flat state layout".to_string(),
                    )
                    .into(),
                    self.stats.clone(),
                )
            })?;

        let next_name = self
            .trace
            .cached_resolved_next_name
            .as_deref()
            .or(self.config.next.as_deref())
            .ok_or_else(|| {
                CheckResult::from_error(
                    RuntimeCheckError::Internal(
                        "compiled BFS interpreter crosscheck missing resolved NEXT name"
                            .to_string(),
                    )
                    .into(),
                    self.stats.clone(),
                )
            })?;

        let (
            template_name,
            template_params,
            template_local,
            template_contains_prime,
            template_has_primed_param,
        ) = {
            let next_def = self.module.op_defs.get(next_name).ok_or_else(|| {
                CheckResult::from_error(
                    RuntimeCheckError::Internal(format!(
                        "compiled BFS interpreter crosscheck could not find NEXT operator {next_name}"
                    ))
                    .into(),
                    self.stats.clone(),
                )
            })?;
            (
                next_def.name.clone(),
                next_def.params.clone(),
                next_def.local,
                next_def.contains_prime,
                next_def.has_primed_param,
            )
        };

        let current_arr = ArrayState::from_state(&parent_state, registry);
        let mut action_def = OperatorDef {
            name: template_name,
            params: template_params,
            body: actions[0].expr.clone(),
            local: template_local,
            contains_prime: template_contains_prime,
            guards_depend_on_prime: false,
            has_primed_param: template_has_primed_param,
            is_recursive: false,
            self_call_count: 0,
        };
        let mut action_successors = Vec::with_capacity(actions.len());

        for (action_idx, action) in actions.into_iter().enumerate() {
            action_def.body = action.expr.clone();
            let successors =
                enumerate_successors(&mut self.ctx, &action_def, &parent_state, &self.module.vars)
                    .map_err(|error| {
                        CheckResult::from_error(
                            RuntimeCheckError::Internal(format!(
                        "compiled BFS interpreter crosscheck failed while enumerating {}: {error}",
                        action.name
                    ))
                            .into(),
                            self.stats.clone(),
                        )
                    })?;

            let mut valid_successors = Vec::new();
            for successor in successors {
                let succ_arr = ArrayState::from_state(&successor, registry);
                let state_ok = self
                    .check_state_constraints_array(&succ_arr)
                    .map_err(|error| CheckResult::from_error(error, self.stats.clone()))?;
                let action_ok = self
                    .check_action_constraints_array(&current_arr, &succ_arr)
                    .map_err(|error| CheckResult::from_error(error, self.stats.clone()))?;
                if state_ok && action_ok {
                    let succ_flat =
                        crate::state::FlatState::from_array_state(&succ_arr, flat_layout.clone());
                    valid_successors.push(succ_flat.buffer().to_vec());
                }
            }
            action_successors.push(CompiledBfsInterpreterActionSuccessors {
                action_idx,
                action_name: action.name,
                successors: valid_successors,
            });
        }

        Ok(action_successors)
    }

    /// Run the compiled BFS level loop, processing flat frontiers through
    /// the compiled BFS step.
    ///
    /// This is the Phase 5 alternative to `run_bfs_loop` that uses the
    /// contiguous arena in `FlatBfsFrontier` and the `CompiledBfsStep` for
    /// native-code action dispatch + fingerprinting + invariant checking.
    ///
    /// Falls back to `run_bfs_loop` if any prerequisite is not met.
    ///
    /// Part of #3988: JIT V2 Phase 5 compiled BFS step.
    pub(in crate::check::model_checker) fn run_compiled_bfs_loop(
        &mut self,
        storage: &mut FingerprintOnlyStorage,
        flat_queue: &mut FlatBfsFrontier,
    ) -> CheckResult {
        // Validate prerequisites -- if any fail, fall back to standard loop.
        if !self.compiled_bfs_level_eligible() {
            if self.llvm2_native_fused_strict_enabled() {
                return self.strict_native_fused_fallback_result(
                    "compiled BFS level is not eligible for this run",
                );
            }
            if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                self.disable_compiled_bfs_for_standard_fallback();
            }
            return self.run_bfs_loop(storage, flat_queue);
        }

        // Part of #4215: Seal the fingerprint algorithm before compiled BFS processing.
        #[cfg(debug_assertions)]
        {
            self.fp_algorithm_sealed = true;
        }

        let registry = self.ctx.var_registry().clone();
        let mut stats = CompiledBfsLoopStats::default();
        let mut depth_limit_reached = false;
        let mut raw_admission_outcomes = Vec::new();

        // Initialize eval arena for sequential BFS.
        tla_eval::eval_arena::init_thread_arena();
        crate::arena::init_worker_arena();

        let use_fused = self.fused_bfs_level_available();
        if self.llvm2_native_fused_strict_enabled() && !self.native_fused_bfs_level_available() {
            return self
                .strict_native_fused_fallback_result("native fused BFS level is unavailable");
        }
        if flat_queue.has_fallback_entries() || flat_queue.remaining_flat_count() == 0 {
            eprintln!("[compiled-bfs] compiled BFS disabled: frontier has no flat parents ready");
            if self.llvm2_native_fused_strict_enabled() {
                return self
                    .strict_native_fused_fallback_result("frontier has no flat parents ready");
            }
            if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                self.disable_compiled_bfs_for_standard_fallback();
            }
            return self.run_bfs_loop(storage, flat_queue);
        }
        if use_fused {
            if let Some(ref level) = self.compiled_bfs_level {
                let parent_count = flat_queue.remaining_flat_count();
                let preflight_result = match flat_queue.remaining_arena() {
                    Some((arena, count)) if count >= parent_count => {
                        level.preflight_fused_arena(arena, parent_count)
                    }
                    _ => Err(tla_jit_runtime::BfsStepError::RuntimeError),
                };
                if let Err(error) = preflight_result {
                    eprintln!("[compiled-bfs] fused level preflight fatal error: {error}");
                    return CheckResult::from_error(
                        RuntimeCheckError::Internal(format!(
                            "compiled BFS fatal error: fused preflight failed: {error}"
                        ))
                        .into(),
                        self.stats.clone(),
                    );
                }
            }
        }
        eprintln!(
            "[compiled-bfs] starting compiled BFS level loop ({} initial states in arena, fused={})",
            flat_queue.len(),
            use_fused,
        );
        stats.execution_started_at = Some(std::time::Instant::now());
        eprintln!(
            "[compiled-bfs] compiled_bfs_step_active={} compiled_bfs_level_active={use_fused}",
            self.compiled_bfs_step.is_some(),
        );

        // Main level loop: process levels until frontier is empty or violation found.
        loop {
            // Check if another portfolio lane has resolved the verdict.
            if let Some(ref sv) = self.portfolio_verdict {
                if sv.is_resolved() {
                    break;
                }
            }
            #[cfg(feature = "z4")]
            if let Some(ref coop) = self.cooperative {
                if coop.verdict.is_resolved() {
                    break;
                }
            }

            // Snapshot the current-level parent count. Successors are appended
            // to the same frontier arena below, so do not keep a borrowed arena
            // slice across enqueue operations.
            if flat_queue.has_fallback_entries() {
                eprintln!(
                    "[compiled-bfs] non-flat fallback entries remain in frontier, \
                     falling back to standard BFS loop"
                );
                if stats.levels_completed > 0
                    || stats.parents_processed > 0
                    || stats.successors_generated > 0
                    || stats.successors_new > 0
                {
                    self.report_compiled_bfs_stats(&stats);
                }
                if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                    self.disable_compiled_bfs_for_standard_fallback();
                }
                if self.llvm2_native_fused_strict_enabled() {
                    return self.strict_native_fused_fallback_result(
                        "non-flat fallback entries remain in the frontier",
                    );
                }
                return self.run_bfs_loop(storage, flat_queue);
            }

            let parent_count = flat_queue.remaining_flat_count();
            if parent_count == 0 {
                break; // Frontier empty -- BFS complete
            }

            if !self.compiled_bfs_step_usable_for_current_graph_mode()
                && !self.fused_bfs_level_available()
            {
                eprintln!(
                    "[compiled-bfs] compiled step and fused level became unavailable, \
                     falling back to standard BFS loop"
                );
                if self.llvm2_native_fused_strict_enabled() {
                    return self.strict_native_fused_fallback_result(
                        "compiled step and fused level became unavailable",
                    );
                }
                self.disable_compiled_bfs_for_standard_fallback();
                return self.run_bfs_loop(storage, flat_queue);
            }

            // Determine successor depth from the first parent's metadata.
            // All parents in this level share the same depth (BFS invariant).
            let (_first_fp, first_depth, _first_trace_loc) = match flat_queue.meta_at_offset(0) {
                Some(m) => m,
                None => {
                    self.report_compiled_bfs_stats(&stats);
                    return CheckResult::from_error(
                        RuntimeCheckError::Internal(format!(
                            "compiled BFS frontier has {parent_count} parents without first-parent metadata"
                        ))
                        .into(),
                        self.stats.clone(),
                    );
                }
            };

            // Depth limit check (all parents share same depth in BFS).
            if let Some(max_depth) = self.exploration.max_depth {
                if first_depth >= max_depth {
                    depth_limit_reached = true;
                    flat_queue.advance_read_cursor(parent_count);
                    stats.levels_completed += 1;
                    continue;
                }
            }

            let succ_depth = match first_depth.checked_add(1) {
                Some(d) => d,
                None => {
                    let error = crate::checker_ops::depth_overflow_error(first_depth);
                    self.report_compiled_bfs_stats(&stats);
                    return CheckResult::from_error(error, self.stats.clone());
                }
            };

            let succ_level = match crate::checker_ops::depth_to_tlc_level(succ_depth) {
                Ok(level) => level,
                Err(error) => {
                    self.report_compiled_bfs_stats(&stats);
                    return CheckResult::from_error(error, self.stats.clone());
                }
            };
            self.ctx.set_tlc_level(succ_level);
            let use_compiled_fingerprint = self.uses_compiled_bfs_fingerprint_domain();

            // Part of #4171: Fused BFS level path — process entire frontier
            // in a single native function call when the fused level is available.
            // Falls back to the per-parent step loop on error.
            if use_fused {
                if let Some(ref level) = self.compiled_bfs_level {
                    let fused_result = match flat_queue.remaining_arena() {
                        Some((arena, count)) if count >= parent_count => {
                            level.run_level_fused_arena(arena, parent_count)
                        }
                        _ => Some(Err(tla_jit_runtime::BfsStepError::RuntimeError)),
                    };

                    match fused_result {
                        Some(Ok(mut level_result)) => {
                            if self.exploration.check_deadlock
                                && level_result.raw_successor_metadata_complete()
                            {
                                if let Some(deadlocked_parent_idx) =
                                    level_result.first_parent_without_raw_successors()
                                {
                                    let expected_processed =
                                        deadlocked_parent_idx.saturating_add(1);
                                    let valid_processed = level_result.parents_processed
                                        == expected_processed
                                        || level_result.parents_processed == parent_count;
                                    if deadlocked_parent_idx >= parent_count || !valid_processed {
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::from_error(
                                            RuntimeCheckError::Internal(format!(
                                                "fused compiled BFS deadlock metadata reported \
                                                 parent {deadlocked_parent_idx} with {} parents \
                                                 processed for current level of {parent_count}",
                                                level_result.parents_processed,
                                            ))
                                            .into(),
                                            self.stats.clone(),
                                        );
                                    }
                                    self.record_transitions(
                                        usize::try_from(level_result.total_generated)
                                            .unwrap_or(usize::MAX),
                                    );
                                    if level_result.total_generated > 0 {
                                        self.stats.max_depth = self.stats.max_depth.max(succ_depth);
                                    }
                                    let parent_slice =
                                        flat_queue.remaining_state_at_offset(deadlocked_parent_idx);
                                    stats.parents_processed +=
                                        level_result.parents_processed as u64;
                                    stats.successors_generated += level_result.total_generated;
                                    stats.successors_new += level_result.total_new;
                                    let Some(parent_slice) = parent_slice else {
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::from_error(
                                            RuntimeCheckError::Internal(
                                                "fused deadlock reported without a parent state"
                                                    .to_string(),
                                            )
                                            .into(),
                                            self.stats.clone(),
                                        );
                                    };
                                    let state = match self
                                        .try_reconstruct_state_from_flat(parent_slice, &registry)
                                    {
                                        Ok(state) => state,
                                        Err(result) => {
                                            self.report_compiled_bfs_stats(&stats);
                                            return result;
                                        }
                                    };
                                    self.report_compiled_bfs_stats(&stats);

                                    return CheckResult::Deadlock {
                                        trace: Trace::from_states(vec![state]),
                                        stats: self.stats.clone(),
                                    };
                                }
                            }

                            if level_result.invariant_ok
                                && level_result.parents_processed != parent_count
                            {
                                self.report_compiled_bfs_stats(&stats);
                                return CheckResult::from_error(
                                    RuntimeCheckError::Internal(format!(
                                        "fused compiled BFS processed {} parents for current \
                                         level of {parent_count}",
                                        level_result.parents_processed,
                                    ))
                                    .into(),
                                    self.stats.clone(),
                                );
                            }

                            if self.exploration.check_deadlock
                                && !level_result.raw_successor_metadata_complete()
                            {
                                if !self.config.constraints.is_empty() {
                                    self.report_compiled_bfs_stats(&stats);
                                    return CheckResult::from_error(
                                        RuntimeCheckError::Internal(
                                            "state-constrained compiled BFS fused level failed \
                                             closed: missing raw-successor metadata for deadlock \
                                             checking"
                                                .to_string(),
                                        )
                                        .into(),
                                        self.stats.clone(),
                                    );
                                }
                                eprintln!(
                                    "[compiled-bfs] fused level lacks raw-successor metadata \
                                     for deadlock checking, falling back to per-parent step"
                                );
                                if self.llvm2_native_fused_strict_enabled() {
                                    self.report_compiled_bfs_stats(&stats);
                                    return self.strict_native_fused_fallback_result(
                                        "fused level lacks raw-successor metadata for deadlock checking",
                                    );
                                }
                                self.compiled_bfs_level = None;
                                if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                                    self.disable_compiled_bfs_for_standard_fallback();
                                    if self.llvm2_native_fused_strict_enabled() {
                                        self.report_compiled_bfs_stats(&stats);
                                        return self.strict_native_fused_fallback_result(
                                            "per-parent compiled step is unavailable after fused metadata fallback",
                                        );
                                    }
                                    return self.run_bfs_loop(storage, flat_queue);
                                }
                                // Fall through to per-parent loop below.
                            } else if self.liveness_cache.cache_for_liveness
                                && !level_result.state_graph_successors_complete()
                            {
                                if !self.config.constraints.is_empty() {
                                    self.report_compiled_bfs_stats(&stats);
                                    return CheckResult::from_error(
                                        RuntimeCheckError::Internal(
                                            "state-constrained compiled BFS fused level failed \
                                             closed: missing complete state-graph successor \
                                             metadata for liveness capture"
                                                .to_string(),
                                        )
                                        .into(),
                                        self.stats.clone(),
                                    );
                                }
                                eprintln!(
                                    "[compiled-bfs] fused level lacks complete successor edge metadata \
                                     for state-graph capture, falling back to per-parent step"
                                );
                                if self.llvm2_native_fused_strict_enabled() {
                                    self.report_compiled_bfs_stats(&stats);
                                    return self.strict_native_fused_fallback_result(
                                        "fused level lacks complete successor edge metadata for state-graph capture",
                                    );
                                }
                                self.compiled_bfs_level = None;
                                if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                                    self.disable_compiled_bfs_for_standard_fallback();
                                    if self.llvm2_native_fused_strict_enabled() {
                                        self.report_compiled_bfs_stats(&stats);
                                        return self.strict_native_fused_fallback_result(
                                            "per-parent compiled step is unavailable after liveness metadata fallback",
                                        );
                                    }
                                    return self.run_bfs_loop(storage, flat_queue);
                                }
                                // Fall through to per-parent loop below.
                            } else {
                                self.record_transitions(
                                    usize::try_from(level_result.total_generated)
                                        .unwrap_or(usize::MAX),
                                );
                                if level_result.total_generated > 0 {
                                    self.stats.max_depth = self.stats.max_depth.max(succ_depth);
                                }
                                // Handle invariant violation from fused level.
                                if !level_result.invariant_ok {
                                    let Some(inv_idx) = level_result.failed_invariant_idx else {
                                        flat_queue.advance_read_cursor(parent_count);
                                        stats.parents_processed +=
                                            level_result.parents_processed as u64;
                                        stats.successors_generated += level_result.total_generated;
                                        stats.successors_new += level_result.total_new;
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::from_error(
                                            RuntimeCheckError::Internal(
                                                "fused compiled BFS reported invariant failure \
                                                 without failed invariant metadata"
                                                    .to_string(),
                                            )
                                            .into(),
                                            self.stats.clone(),
                                        );
                                    };
                                    let Some(failed_parent_idx) = level_result.failed_parent_idx
                                    else {
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::from_error(
                                            RuntimeCheckError::Internal(
                                                "fused compiled BFS reported invariant failure \
                                                 without failed parent metadata"
                                                    .to_string(),
                                            )
                                            .into(),
                                            self.stats.clone(),
                                        );
                                    };
                                    let expected_processed = failed_parent_idx.saturating_add(1);
                                    if failed_parent_idx >= parent_count
                                        || level_result.parents_processed != expected_processed
                                    {
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::from_error(
                                            RuntimeCheckError::Internal(format!(
                                                "fused compiled BFS invariant metadata reported \
                                                 parent {failed_parent_idx} with {} parents \
                                                 processed for current level of {parent_count}",
                                                level_result.parents_processed,
                                            ))
                                            .into(),
                                            self.stats.clone(),
                                        );
                                    }
                                    let inv_name = self
                                        .config
                                        .invariants
                                        .get(inv_idx as usize)
                                        .cloned()
                                        .unwrap_or_else(|| format!("invariant_{inv_idx}"));

                                    let Some(failed_successor) = level_result.failed_successor()
                                    else {
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::from_error(
                                            RuntimeCheckError::Internal(
                                                "fused compiled BFS reported invariant failure \
                                                 without failed successor metadata"
                                                    .to_string(),
                                            )
                                            .into(),
                                            self.stats.clone(),
                                        );
                                    };
                                    let state_result = self.try_reconstruct_state_from_flat(
                                        failed_successor,
                                        &registry,
                                    );

                                    flat_queue.advance_read_cursor(parent_count);
                                    stats.parents_processed +=
                                        level_result.parents_processed as u64;
                                    stats.successors_generated += level_result.total_generated;
                                    stats.successors_new += level_result.total_new;
                                    let state = match state_result {
                                        Ok(state) => state,
                                        Err(result) => {
                                            self.report_compiled_bfs_stats(&stats);
                                            return result;
                                        }
                                    };
                                    self.report_compiled_bfs_stats(&stats);

                                    return CheckResult::InvariantViolation {
                                        invariant: inv_name,
                                        trace: Trace::from_states(vec![state]),
                                        stats: self.stats.clone(),
                                    };
                                }

                                // Process the fused level's successors through global dedup.
                                // Clone the bridge to avoid holding an immutable borrow on
                                // `self.flat_bfs_adapter` while calling mutable methods below.
                                let bridge = self
                                    .flat_bfs_adapter
                                    .as_ref()
                                    .map(|adapter| adapter.bridge().clone());

                                debug_assert_eq!(
                                    level_result.successor_count() as u64,
                                    level_result.total_new,
                                    "fused level arena count must match backend new count",
                                );
                                let mut compiled_fingerprint_successors_validated_once =
                                    if use_compiled_fingerprint {
                                        let Some(bridge) = bridge.as_ref() else {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(
                                                    "compiled BFS flat fingerprinting requested \
                                                     without a FlatBfsAdapter"
                                                        .to_string(),
                                                )
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        };
                                        if level_result.state_len() != bridge.num_slots() {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            self.report_compiled_bfs_stats(&stats);
                                            return self.flat_reconstruction_error_result(
                                                "fused compiled BFS successor width mismatch",
                                                format!(
                                                    "backend returned {} i64 slots per state, \
                                                     adapter expects {}",
                                                    level_result.state_len(),
                                                    bridge.num_slots(),
                                                ),
                                            );
                                        }
                                        true
                                    } else {
                                        false
                                    };
                                if let Some(bridge) = bridge.as_ref() {
                                    if bridge.raw_admission_validation_required() {
                                        if let Err(error) =
                                            level_result.for_each_successor_mut(|succ_buf| {
                                                bridge
                                                    .canonicalize_raw_buffer_for_admission(succ_buf)
                                            })
                                        {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            self.report_compiled_bfs_stats(&stats);
                                            return self.flat_reconstruction_error_result(
                                                "failed to canonicalize fused compiled BFS \
                                                 successor buffer",
                                                error,
                                            );
                                        }
                                        compiled_fingerprint_successors_validated_once = false;
                                    }
                                }
                                let mut global_new: u64 = 0;
                                let mut fused_succ_processed: u64 = 0;
                                let mut liveness_successors = self
                                    .liveness_cache
                                    .cache_for_liveness
                                    .then(|| vec![Vec::new(); parent_count]);
                                let needs_rust_regular_invariant_check =
                                    fused_successor_needs_rust_regular_invariant_check(
                                        level_result.regular_invariants_checked_by_backend(),
                                        self.config.invariants.len(),
                                    );
                                let needs_pre_seen_lookup = fused_successor_needs_pre_seen_lookup(
                                    level_result.regular_invariants_checked_by_backend(),
                                    self.config.invariants.len(),
                                );
                                let needs_trace_invariant_check =
                                    !self.config.trace_invariants.is_empty();
                                let successor_parent_indices_complete =
                                    level_result.successor_parent_indices_complete();
                                let use_batch_admission = !needs_pre_seen_lookup
                                    && !needs_rust_regular_invariant_check
                                    && !needs_trace_invariant_check
                                    && successor_parent_indices_complete;
                                if use_batch_admission {
                                    let borrowed_batch_inputs = if use_compiled_fingerprint {
                                        level_result
                                            .successor_fingerprint_values()
                                            .zip(level_result.successor_parent_indices())
                                    } else {
                                        None
                                    };
                                    if let Some((batch_fp_values, parent_indices)) =
                                        borrowed_batch_inputs
                                    {
                                        let successor_count = level_result.successor_count();

                                        for successor_idx in 0..successor_count {
                                            // Part of #4203: Periodic state_count update within the
                                            // fused successor dedup loop. The fused path processes all
                                            // parents in native code, so per-parent updates are not
                                            // possible. Instead, update every
                                            // COMPILED_BFS_PROGRESS_INTERVAL successors to keep stats
                                            // fresh for memory pressure checks.
                                            fused_succ_processed += 1;
                                            if fused_succ_processed % COMPILED_BFS_PROGRESS_INTERVAL
                                                == 0
                                            {
                                                self.stats.states_found = self.states_count();
                                            }

                                            if compiled_fingerprint_successors_validated_once {
                                                stats.fused_admission_validations_elided += 1;
                                            }

                                            stats.fused_pre_seen_lookups_skipped += 1;
                                            let Some(parent_idx) =
                                                parent_indices.get(successor_idx)
                                            else {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(
                                                        "fused compiled BFS batch admission \
                                                         requested without successor parent metadata"
                                                            .to_string(),
                                                    )
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            };
                                            if parent_idx >= parent_count {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS batch admission reported \
                                                         parent index {parent_idx} for {parent_count} \
                                                         parents"
                                                    ))
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            }
                                            if flat_queue.meta_at_offset(parent_idx).is_none() {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS batch admission missing \
                                                         parent metadata at index {parent_idx}",
                                                    ))
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            }

                                            if let Some(ref mut by_parent) = liveness_successors {
                                                let Some(successors) =
                                                    by_parent.get_mut(parent_idx)
                                                else {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return CheckResult::from_error(
                                                        RuntimeCheckError::Internal(format!(
                                                            "fused compiled BFS state-graph capture \
                                                             reported parent index {parent_idx} for \
                                                             {parent_count} parents",
                                                        ))
                                                        .into(),
                                                        self.stats.clone(),
                                                    );
                                                };
                                                successors.push(Fingerprint(
                                                    batch_fp_values[successor_idx],
                                                ));
                                            }
                                        }

                                        if let Err(error) = flat_queue
                                            .try_reserve_raw_buffers(batch_fp_values.len())
                                        {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                    "compiled BFS batch admission could not reserve \
                                                     successor frontier capacity before global \
                                                     admission: {error}"
                                                ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        }

                                        self.state_storage
                                            .seen_fps
                                            .insert_batch_fingerprint_values_checked_into(
                                                batch_fp_values,
                                                &mut raw_admission_outcomes,
                                            );
                                        let outcomes = &raw_admission_outcomes;
                                        if outcomes.len() > batch_fp_values.len() {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                    "compiled BFS batch admission returned {} outcomes \
                                                     for {} fingerprints",
                                                    outcomes.len(),
                                                    batch_fp_values.len(),
                                                ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        }

                                        let outcome_count = outcomes.len();
                                        let mut storage_fault = None;
                                        let successor_arena = level_result.successor_arena_slice();
                                        let successor_state_len = level_result.state_len();
                                        let successor_count = level_result.successor_count();
                                        for (successor_idx, outcome) in outcomes.iter().enumerate()
                                        {
                                            let succ_fp =
                                                Fingerprint(batch_fp_values[successor_idx]);
                                            match outcome {
                                                InsertOutcome::Inserted => {
                                                    let parent_idx =
                                                        parent_indices.get(successor_idx).expect(
                                                            "compiled BFS borrowed batch parent \
                                                             index was validated",
                                                        );
                                                    let (parent_fp, _depth, parent_trace_loc) =
                                                        flat_queue
                                                            .meta_at_offset(parent_idx)
                                                            .expect(
                                                                "compiled BFS borrowed batch \
                                                                 parent metadata was validated",
                                                            );
                                                    let trace_loc = match self
                                                        .record_fp_only_batch_admission_bookkeeping(
                                                            succ_fp,
                                                            Some(parent_fp),
                                                            Some(parent_trace_loc),
                                                            succ_depth,
                                                        ) {
                                                        Ok(loc) => loc,
                                                        Err(result) => {
                                                            flat_queue
                                                                .advance_read_cursor(parent_count);
                                                            stats.parents_processed += level_result
                                                                .parents_processed
                                                                as u64;
                                                            stats.successors_generated +=
                                                                level_result.total_generated;
                                                            stats.successors_new +=
                                                                level_result.total_new;
                                                            self.report_compiled_bfs_stats(&stats);
                                                            return result;
                                                        }
                                                    };
                                                    flat_queue.push_raw_buffer_from_arena_index(
                                                        successor_arena,
                                                        successor_state_len,
                                                        successor_count,
                                                        successor_idx,
                                                        succ_fp,
                                                        succ_depth,
                                                        trace_loc,
                                                    );
                                                    global_new += 1;
                                                    self.stats.max_depth =
                                                        self.stats.max_depth.max(succ_depth);
                                                }
                                                InsertOutcome::AlreadyPresent => {}
                                                InsertOutcome::StorageFault(fault) => {
                                                    storage_fault = Some(fault.clone());
                                                    break;
                                                }
                                                _ => unreachable!(),
                                            }
                                        }

                                        if let Some(fault) = storage_fault {
                                            self.stats.states_found = self.states_count();
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return self.storage_fault_result(fault);
                                        }

                                        if outcome_count != batch_fp_values.len() {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                    "compiled BFS batch admission returned {} outcomes \
                                                     for {} fingerprints",
                                                    outcome_count,
                                                    batch_fp_values.len(),
                                                ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        }
                                    } else {
                                        let successor_count = level_result.successor_count();
                                        let Some(parent_indices) =
                                            level_result.successor_parent_indices()
                                        else {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(
                                                    "fused compiled BFS batch admission requested \
                                                     without complete successor parent metadata"
                                                        .to_string(),
                                                )
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        };
                                        let mut batch_fps = Vec::with_capacity(successor_count);

                                        for (successor_idx, succ_buf) in
                                            level_result.iter_successors().enumerate()
                                        {
                                            // Part of #4203: Periodic state_count update within the
                                            // fused successor dedup loop. The fused path processes all
                                            // parents in native code, so per-parent updates are not
                                            // possible. Instead, update every
                                            // COMPILED_BFS_PROGRESS_INTERVAL successors to keep stats
                                            // fresh for memory pressure checks.
                                            fused_succ_processed += 1;
                                            if fused_succ_processed % COMPILED_BFS_PROGRESS_INTERVAL
                                                == 0
                                            {
                                                self.stats.states_found = self.states_count();
                                            }

                                            if compiled_fingerprint_successors_validated_once {
                                                stats.fused_admission_validations_elided += 1;
                                            }

                                            // Part of #3987: Use compiled xxh3 when active —
                                            // single SIMD hash of raw i64 buffer, no per-variable
                                            // type dispatch. Falls back to FP64 otherwise.
                                            let succ_fp = if use_compiled_fingerprint {
                                                level_result
                                                .successor_fingerprint_at(successor_idx)
                                                .unwrap_or_else(|| {
                                                    super::super::invariants::fingerprint_flat_compiled(
                                                        succ_buf,
                                                    )
                                                })
                                            } else {
                                                let Some(bridge) = bridge.as_ref() else {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(
                                                        "compiled BFS traditional fingerprinting \
                                                         requested without a FlatBfsAdapter"
                                                            .to_string(),
                                                    )
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                                };
                                                match bridge
                                                    .try_traditional_fingerprint_from_buffer(
                                                        succ_buf, &registry,
                                                    ) {
                                                    Ok(fp) => fp,
                                                    Err(error) => {
                                                        flat_queue
                                                            .advance_read_cursor(parent_count);
                                                        stats.parents_processed +=
                                                            level_result.parents_processed as u64;
                                                        stats.successors_generated +=
                                                            level_result.total_generated;
                                                        stats.successors_new += global_new;
                                                        self.report_compiled_bfs_stats(&stats);
                                                        return self.flat_reconstruction_error_result(
                                                        "failed to fingerprint fused compiled BFS \
                                                         successor buffer",
                                                        error,
                                                    );
                                                    }
                                                }
                                            };

                                            if let Some(ref mut by_parent) = liveness_successors {
                                                let Some(parent_idx) =
                                                    parent_indices.get(successor_idx)
                                                else {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(
                                                        "fused compiled BFS state-graph capture \
                                                         requested without successor parent metadata"
                                                            .to_string(),
                                                    )
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                                };
                                                let Some(successors) =
                                                    by_parent.get_mut(parent_idx)
                                                else {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return CheckResult::from_error(
                                                        RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS state-graph capture \
                                                         reported parent index {parent_idx} for \
                                                         {parent_count} parents",
                                                    ))
                                                        .into(),
                                                        self.stats.clone(),
                                                    );
                                                };
                                                successors.push(succ_fp);
                                            }

                                            stats.fused_pre_seen_lookups_skipped += 1;
                                            let Some(parent_idx) =
                                                parent_indices.get(successor_idx)
                                            else {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                RuntimeCheckError::Internal(
                                                    "fused compiled BFS batch admission requested \
                                                     without successor parent metadata"
                                                        .to_string(),
                                                )
                                                .into(),
                                                self.stats.clone(),
                                            );
                                            };
                                            if parent_idx >= parent_count {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS batch admission reported \
                                                         parent index {parent_idx} for {parent_count} \
                                                         parents"
                                                    ))
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            }
                                            if flat_queue.meta_at_offset(parent_idx).is_none() {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS batch admission reported \
                                                         parent index {parent_idx} for {parent_count} \
                                                         parents"
                                                    ))
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            }
                                            batch_fps.push(succ_fp);
                                        }

                                        if let Err(error) =
                                            flat_queue.try_reserve_raw_buffers(successor_count)
                                        {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                    "compiled BFS batch admission could not reserve \
                                                     successor frontier capacity before global \
                                                     admission: {error}"
                                                ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        }

                                        let outcomes = self
                                            .state_storage
                                            .seen_fps
                                            .insert_batch_checked(&batch_fps);
                                        if outcomes.len() > batch_fps.len() {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                "compiled BFS batch admission returned {} outcomes \
                                                 for {} fingerprints",
                                                outcomes.len(),
                                                batch_fps.len(),
                                            ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        }

                                        let outcome_count = outcomes.len();
                                        let mut storage_fault = None;
                                        let successor_arena = level_result.successor_arena_slice();
                                        let successor_state_len = level_result.state_len();
                                        let successor_count = level_result.successor_count();
                                        for (successor_idx, outcome) in
                                            outcomes.into_iter().enumerate()
                                        {
                                            let succ_fp = batch_fps[successor_idx];
                                            match outcome {
                                                InsertOutcome::Inserted => {
                                                    let parent_idx =
                                                        parent_indices.get(successor_idx).expect(
                                                            "compiled BFS batch parent index was validated",
                                                        );
                                                    let (parent_fp, _depth, parent_trace_loc) =
                                                        flat_queue
                                                            .meta_at_offset(parent_idx)
                                                            .expect(
                                                                "compiled BFS batch parent \
                                                                 metadata was validated",
                                                            );
                                                    let trace_loc = match self
                                                        .record_fp_only_batch_admission_bookkeeping(
                                                            succ_fp,
                                                            Some(parent_fp),
                                                            Some(parent_trace_loc),
                                                            succ_depth,
                                                        ) {
                                                        Ok(loc) => loc,
                                                        Err(result) => {
                                                            flat_queue
                                                                .advance_read_cursor(parent_count);
                                                            stats.parents_processed += level_result
                                                                .parents_processed
                                                                as u64;
                                                            stats.successors_generated +=
                                                                level_result.total_generated;
                                                            stats.successors_new +=
                                                                level_result.total_new;
                                                            self.report_compiled_bfs_stats(&stats);
                                                            return result;
                                                        }
                                                    };
                                                    flat_queue.push_raw_buffer_from_arena_index(
                                                        successor_arena,
                                                        successor_state_len,
                                                        successor_count,
                                                        successor_idx,
                                                        succ_fp,
                                                        succ_depth,
                                                        trace_loc,
                                                    );
                                                    global_new += 1;
                                                    self.stats.max_depth =
                                                        self.stats.max_depth.max(succ_depth);
                                                }
                                                InsertOutcome::AlreadyPresent => {}
                                                InsertOutcome::StorageFault(fault) => {
                                                    storage_fault = Some(fault);
                                                    break;
                                                }
                                                _ => unreachable!(),
                                            }
                                        }

                                        if let Some(fault) = storage_fault {
                                            self.stats.states_found = self.states_count();
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return self.storage_fault_result(fault);
                                        }

                                        if outcome_count != batch_fps.len() {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                "compiled BFS batch admission returned {} outcomes \
                                                 for {} fingerprints",
                                                outcome_count,
                                                batch_fps.len(),
                                            ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        }
                                    }
                                } else {
                                    for (successor_idx, (parent_idx, succ_buf)) in level_result
                                        .iter_successors_with_parent_indices()
                                        .enumerate()
                                    {
                                        // Part of #4203: Periodic state_count update within the
                                        // fused successor dedup loop. The fused path processes all
                                        // parents in native code, so per-parent updates are not
                                        // possible. Instead, update every
                                        // COMPILED_BFS_PROGRESS_INTERVAL successors to keep stats
                                        // fresh for memory pressure checks.
                                        fused_succ_processed += 1;
                                        if fused_succ_processed % COMPILED_BFS_PROGRESS_INTERVAL
                                            == 0
                                        {
                                            self.stats.states_found = self.states_count();
                                        }

                                        if compiled_fingerprint_successors_validated_once {
                                            stats.fused_admission_validations_elided += 1;
                                        }

                                        // Part of #3987: Use compiled xxh3 when active —
                                        // single SIMD hash of raw i64 buffer, no per-variable
                                        // type dispatch. Falls back to FP64 otherwise.
                                        let succ_fp = if use_compiled_fingerprint {
                                            level_result
                                            .successor_fingerprint_at(successor_idx)
                                            .unwrap_or_else(|| {
                                                super::super::invariants::fingerprint_flat_compiled(
                                                    succ_buf,
                                                )
                                            })
                                        } else {
                                            let Some(bridge) = bridge.as_ref() else {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(
                                                        "compiled BFS traditional fingerprinting \
                                                     requested without a FlatBfsAdapter"
                                                            .to_string(),
                                                    )
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            };
                                            match bridge.try_traditional_fingerprint_from_buffer(
                                                succ_buf, &registry,
                                            ) {
                                                Ok(fp) => fp,
                                                Err(error) => {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return self.flat_reconstruction_error_result(
                                                        "failed to fingerprint fused compiled BFS \
                                                     successor buffer",
                                                        error,
                                                    );
                                                }
                                            }
                                        };

                                        let parent_idx = match parent_idx {
                                            Some(parent_idx) if parent_idx < parent_count => {
                                                parent_idx
                                            }
                                            Some(parent_idx) => {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS successor reported \
                                                         parent index {parent_idx} for \
                                                         {parent_count} parents",
                                                    ))
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            }
                                            None => {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(
                                                        "fused compiled BFS successor admission \
                                                         requested without successor parent metadata"
                                                            .to_string(),
                                                    )
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            }
                                        };
                                        let Some((parent_fp, _depth, parent_trace_loc)) =
                                            flat_queue.meta_at_offset(parent_idx)
                                        else {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                    "fused compiled BFS successor admission \
                                                     missing parent metadata at index {parent_idx}",
                                                ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        };

                                        if let Some(ref mut by_parent) = liveness_successors {
                                            let Some(successors) = by_parent.get_mut(parent_idx)
                                            else {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    RuntimeCheckError::Internal(format!(
                                                        "fused compiled BFS state-graph capture \
                                                     reported parent index {parent_idx} for \
                                                     {parent_count} parents",
                                                    ))
                                                    .into(),
                                                    self.stats.clone(),
                                                );
                                            };
                                            successors.push(succ_fp);
                                        }

                                        // Global dedup check.
                                        if needs_pre_seen_lookup {
                                            stats.fused_pre_seen_lookups += 1;
                                            match self.is_state_seen_checked(succ_fp) {
                                                Ok(true) => continue,
                                                Ok(false) => {}
                                                Err(result) => {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return result;
                                                }
                                            }
                                        } else {
                                            stats.fused_pre_seen_lookups_skipped += 1;
                                            debug_assert!(
                                                !needs_rust_regular_invariant_check,
                                                "pre-seen lookup may be skipped only when no Rust-side \
                                             regular invariant check is needed before admission"
                                            );
                                        }

                                        let parent_fp_for_invariant = parent_fp;

                                        let mut succ_array_for_invariants = None;
                                        if needs_rust_regular_invariant_check
                                            || needs_trace_invariant_check
                                        {
                                            succ_array_for_invariants = Some(
                                                match self.try_reconstruct_array_state_from_flat(
                                                    succ_buf, &registry,
                                                ) {
                                                    Ok(succ_array) => succ_array,
                                                    Err(result) => {
                                                        flat_queue
                                                            .advance_read_cursor(parent_count);
                                                        stats.parents_processed +=
                                                            level_result.parents_processed as u64;
                                                        stats.successors_generated +=
                                                            level_result.total_generated;
                                                        stats.successors_new += global_new;
                                                        self.report_compiled_bfs_stats(&stats);
                                                        return result;
                                                    }
                                                },
                                            );
                                        }

                                        if needs_rust_regular_invariant_check {
                                            let succ_array =
                                                succ_array_for_invariants.as_ref().expect(
                                                    "successor reconstructed for invariant check",
                                                );
                                            match self.check_successor_invariant(
                                            parent_fp_for_invariant,
                                            succ_array,
                                            succ_fp,
                                            succ_level,
                                        ) {
                                            crate::checker_ops::InvariantOutcome::Ok
                                            | crate::checker_ops::InvariantOutcome::ViolationContinued => {}
                                            crate::checker_ops::InvariantOutcome::Violation {
                                                invariant,
                                                ..
                                            } => {
                                                let previous_parent_trace_loc =
                                                    self.trace.current_parent_trace_loc;
                                                self.trace.current_parent_trace_loc =
                                                    Some(parent_trace_loc);
                                                let stage_result =
                                                    self.stage_successor_for_terminal_trace(
                                                        parent_fp_for_invariant,
                                                        succ_array,
                                                        succ_fp,
                                                        succ_depth,
                                                    );
                                                self.trace.current_parent_trace_loc =
                                                    previous_parent_trace_loc;
                                                if let Err(result) = stage_result {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return self
                                                        .finalize_terminal_result_with_storage(result);
                                                }
                                                if let Some(result) = self
                                                    .handle_invariant_violation(
                                                        invariant, succ_fp, succ_depth,
                                                    )
                                                {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return result;
                                                }
                                            }
                                            crate::checker_ops::InvariantOutcome::Error(error) => {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                stats.successors_generated +=
                                                    level_result.total_generated;
                                                stats.successors_new += global_new;
                                                self.report_compiled_bfs_stats(&stats);
                                                return CheckResult::from_error(
                                                    error,
                                                    self.stats.clone(),
                                                );
                                            }
                                        }
                                        }

                                        if needs_trace_invariant_check {
                                            let succ_array = succ_array_for_invariants
                                                .as_ref()
                                                .expect(
                                                "successor reconstructed for trace invariant check",
                                            );
                                            match self.check_trace_invariants(
                                                parent_fp_for_invariant,
                                                succ_array,
                                                succ_fp,
                                            ) {
                                                TraceInvariantOutcome::Ok => {}
                                                TraceInvariantOutcome::Violation {
                                                    invariant,
                                                    trace,
                                                } => {
                                                    let previous_parent_trace_loc =
                                                        self.trace.current_parent_trace_loc;
                                                    self.trace.current_parent_trace_loc =
                                                        Some(parent_trace_loc);
                                                    let stage_result = self
                                                        .stage_successor_for_terminal_trace(
                                                            parent_fp_for_invariant,
                                                            succ_array,
                                                            succ_fp,
                                                            succ_depth,
                                                        );
                                                    self.trace.current_parent_trace_loc =
                                                        previous_parent_trace_loc;
                                                    if let Err(result) = stage_result {
                                                        flat_queue
                                                            .advance_read_cursor(parent_count);
                                                        stats.parents_processed +=
                                                            level_result.parents_processed as u64;
                                                        stats.successors_generated +=
                                                            level_result.total_generated;
                                                        stats.successors_new += global_new;
                                                        self.report_compiled_bfs_stats(&stats);
                                                        return self
                                                            .finalize_terminal_result_with_storage(
                                                                result,
                                                            );
                                                    }
                                                    self.stats.max_depth =
                                                        self.stats.max_depth.max(succ_depth);
                                                    self.stats.states_found = self.states_count();
                                                    self.update_coverage_totals();
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    let result = CheckResult::InvariantViolation {
                                                        invariant,
                                                        trace,
                                                        stats: self.stats.clone(),
                                                    };
                                                    return self.finalize_terminal_result(result);
                                                }
                                                TraceInvariantOutcome::Error(error) => {
                                                    flat_queue.advance_read_cursor(parent_count);
                                                    stats.parents_processed +=
                                                        level_result.parents_processed as u64;
                                                    stats.successors_generated +=
                                                        level_result.total_generated;
                                                    stats.successors_new += global_new;
                                                    self.report_compiled_bfs_stats(&stats);
                                                    return CheckResult::from_error(
                                                        error,
                                                        self.stats.clone(),
                                                    );
                                                }
                                            }
                                        }

                                        let previous_parent_trace_loc =
                                            self.trace.current_parent_trace_loc;
                                        self.trace.current_parent_trace_loc =
                                            Some(parent_trace_loc);
                                        let mark_result = self.mark_state_seen_fp_only_checked(
                                            succ_fp,
                                            Some(parent_fp),
                                            succ_depth,
                                        );
                                        self.trace.current_parent_trace_loc =
                                            previous_parent_trace_loc;

                                        match mark_result {
                                            Ok(true) => {}
                                            Ok(false) => continue,
                                            Err(result) => {
                                                flat_queue.advance_read_cursor(parent_count);
                                                stats.parents_processed +=
                                                    level_result.parents_processed as u64;
                                                self.report_compiled_bfs_stats(&stats);
                                                return result;
                                            }
                                        }

                                        global_new += 1;
                                        let trace_loc = self.trace.last_inserted_trace_loc;
                                        self.stats.max_depth = self.stats.max_depth.max(succ_depth);
                                        flat_queue.push_raw_buffer(
                                            succ_buf, succ_fp, succ_depth, trace_loc,
                                        );
                                    }
                                }

                                if let Some(by_parent) = liveness_successors {
                                    for (parent_idx, successors) in
                                        by_parent.into_iter().enumerate()
                                    {
                                        let Some((parent_fp, _depth, _trace_loc)) =
                                            flat_queue.meta_at_offset(parent_idx)
                                        else {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                RuntimeCheckError::Internal(format!(
                                                    "fused compiled BFS state-graph capture \
                                                     missing parent metadata at index {parent_idx}",
                                                ))
                                                .into(),
                                                self.stats.clone(),
                                            );
                                        };
                                        if let Err(error) = self
                                            .liveness_cache
                                            .successors
                                            .insert(parent_fp, successors)
                                        {
                                            flat_queue.advance_read_cursor(parent_count);
                                            stats.parents_processed +=
                                                level_result.parents_processed as u64;
                                            stats.successors_generated +=
                                                level_result.total_generated;
                                            stats.successors_new += global_new;
                                            self.report_compiled_bfs_stats(&stats);
                                            return CheckResult::from_error(
                                                error,
                                                self.stats.clone(),
                                            );
                                        }
                                    }
                                }

                                flat_queue.advance_read_cursor(parent_count);
                                stats.parents_processed += level_result.parents_processed as u64;
                                stats.successors_generated += level_result.total_generated;
                                stats.successors_new += global_new;
                                stats.levels_completed += 1;

                                // State limit check after level.
                                if let Some(max_states) = self.exploration.max_states {
                                    if self.states_count() >= max_states {
                                        depth_limit_reached = true;
                                    }
                                }

                                // Update model checker stats and progress.
                                let total_states = self.states_count();
                                self.stats.states_found = total_states;
                                if stats.levels_completed % 5 == 0 {
                                    eprintln!(
                                        "[compiled-bfs] fused level {}: {} states, {} generated, {} new, queue={}",
                                        stats.levels_completed,
                                        total_states,
                                        stats.successors_generated,
                                        stats.successors_new,
                                        flat_queue.len(),
                                    );
                                }

                                // Part of #4203: Memory pressure check after fused level.
                                // Fused levels process many parents at once; check OOM
                                // before starting the next level.
                                if let Some(ref policy) = self.exploration.memory_policy {
                                    use crate::memory::MemoryPressure;
                                    if policy.check() == MemoryPressure::Critical {
                                        let rss_mb = crate::memory::current_rss_bytes()
                                            .map(|b| b / (1024 * 1024))
                                            .unwrap_or(0);
                                        let limit_mb = policy.limit_bytes() / (1024 * 1024);
                                        eprintln!(
                                            "[compiled-bfs] memory critical ({rss_mb} MB / {limit_mb} MB limit) \
                                         after fused level {} — stopping.",
                                            stats.levels_completed,
                                        );
                                        self.report_compiled_bfs_stats(&stats);
                                        return CheckResult::LimitReached {
                                            limit_type: super::super::LimitType::Memory,
                                            stats: self.stats.clone(),
                                        };
                                    }
                                }

                                crate::arena::worker_arena_reset();

                                if depth_limit_reached {
                                    break;
                                }
                                continue;
                            }
                        }
                        Some(Err(e @ tla_jit_runtime::BfsStepError::FatalRuntimeError)) => {
                            eprintln!("[compiled-bfs] fused level fatal error: {e}");
                            self.report_compiled_bfs_stats(&stats);
                            return CheckResult::from_error(
                                RuntimeCheckError::Internal(format!(
                                    "compiled BFS fatal error: {e}"
                                ))
                                .into(),
                                self.stats.clone(),
                            );
                        }
                        Some(Err(e)) => {
                            eprintln!(
                                "[compiled-bfs] fused level error: {e} — \
                                 falling back to per-parent step"
                            );
                            if self.llvm2_native_fused_strict_enabled() {
                                self.report_compiled_bfs_stats(&stats);
                                return self.strict_native_fused_fallback_result(format!(
                                    "fused level returned recoverable error: {e}"
                                ));
                            }
                            if !self.config.constraints.is_empty() {
                                self.report_compiled_bfs_stats(&stats);
                                return CheckResult::from_error(
                                    RuntimeCheckError::Internal(format!(
                                        "state-constrained compiled BFS fused level failed \
                                         closed: {e}"
                                    ))
                                    .into(),
                                    self.stats.clone(),
                                );
                            }
                            if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                                self.disable_compiled_bfs_for_standard_fallback();
                                if self.llvm2_native_fused_strict_enabled() {
                                    self.report_compiled_bfs_stats(&stats);
                                    return self.strict_native_fused_fallback_result(
                                        "per-parent compiled step is unavailable after fused error",
                                    );
                                }
                                return self.run_bfs_loop(storage, flat_queue);
                            }
                            // Fall through to per-parent loop below.
                        }
                        None => {
                            // Fused function not available (shouldn't happen
                            // since use_fused checked has_fused_level).
                            if !self.config.constraints.is_empty() {
                                self.report_compiled_bfs_stats(&stats);
                                return CheckResult::from_error(
                                    RuntimeCheckError::Internal(
                                        "state-constrained compiled BFS fused level became \
                                         unavailable after eligibility"
                                            .to_string(),
                                    )
                                    .into(),
                                    self.stats.clone(),
                                );
                            }
                            if !self.compiled_bfs_step_usable_for_current_graph_mode() {
                                self.disable_compiled_bfs_for_standard_fallback();
                                if self.llvm2_native_fused_strict_enabled() {
                                    self.report_compiled_bfs_stats(&stats);
                                    return self.strict_native_fused_fallback_result(
                                        "per-parent compiled step is unavailable after fused level disappeared",
                                    );
                                }
                                return self.run_bfs_loop(storage, flat_queue);
                            }
                            eprintln!(
                                "[compiled-bfs] fused level returned None after availability \
                                 check; falling back to per-parent step"
                            );
                            if self.llvm2_native_fused_strict_enabled() {
                                self.report_compiled_bfs_stats(&stats);
                                return self.strict_native_fused_fallback_result(
                                    "fused level returned None after availability check",
                                );
                            }
                        }
                    }
                }
            }

            // Per-parent step loop (fallback when fused path not available or failed).
            let mut level_generated: u64 = 0;
            let mut level_new: u64 = 0;
            let mut level_parents: u64 = 0;
            let mut early_break = false;
            let mut consumed_count = parent_count; // default: consume all
            let crosscheck_with_interpreter =
                std::env::var_os(COMPILED_BFS_INTERPRETER_CROSSCHECK_ENV).is_some();
            let mut step_scratch = {
                let step = self
                    .compiled_bfs_step
                    .as_ref()
                    .expect("invariant: compiled_bfs_step present in compiled BFS loop");
                CompiledBfsStepScratch::new(step.state_len())
            };

            for parent_idx in 0..parent_count {
                // State limit check.
                if let Some(max_states) = self.exploration.max_states {
                    if self.states_count() >= max_states {
                        depth_limit_reached = true;
                        consumed_count = parent_idx;
                        early_break = true;
                        break;
                    }
                }

                // Execute the compiled BFS step.
                let mut crosscheck_parent = None;
                let output = {
                    let parent_slice = match flat_queue.remaining_state_at_offset(parent_idx) {
                        Some(parent_slice) => parent_slice,
                        None => {
                            eprintln!(
                                "[compiled-bfs] missing parent {parent_idx} of current level, \
                                 falling back to standard BFS loop"
                            );
                            if self.llvm2_native_fused_strict_enabled() {
                                flat_queue.advance_read_cursor(parent_idx);
                                stats.parents_processed += level_parents;
                                stats.successors_generated += level_generated;
                                stats.successors_new += level_new;
                                self.report_compiled_bfs_stats(&stats);
                                return self.strict_native_fused_fallback_result(format!(
                                    "missing parent {parent_idx} of current level"
                                ));
                            }
                            flat_queue.advance_read_cursor(parent_idx);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return self.run_bfs_loop(storage, flat_queue);
                        }
                    };
                    if crosscheck_with_interpreter {
                        crosscheck_parent = Some(parent_slice.to_vec());
                    }
                    let step = self
                        .compiled_bfs_step
                        .as_ref()
                        .expect("invariant: compiled_bfs_step present in compiled BFS loop");
                    step.step_flat_scoped(parent_slice, &mut step_scratch)
                };

                let output = match output {
                    Ok(output) => output,
                    Err(e @ tla_jit_runtime::BfsStepError::FatalRuntimeError) => {
                        eprintln!(
                            "[compiled-bfs] step fatal error at depth {first_depth}, \
                             parent {parent_idx}: {e}"
                        );
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(format!("compiled BFS fatal error: {e}"))
                                .into(),
                            self.stats.clone(),
                        );
                    }
                    Err(e) => {
                        eprintln!(
                            "[compiled-bfs] step error at depth {first_depth}, \
                             parent {parent_idx}: {e} -- disabling"
                        );
                        if self.llvm2_native_fused_strict_enabled() {
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return self.strict_native_fused_fallback_result(format!(
                                "per-parent compiled step returned recoverable error: {e}"
                            ));
                        }
                        self.jit_monolithic_disabled = true;
                        self.compiled_bfs_step = None;
                        self.compiled_bfs_level = None;
                        // Advance cursor past processed parents, fall back for rest.
                        flat_queue.advance_read_cursor(parent_idx);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return self.run_bfs_loop(storage, flat_queue);
                    }
                };
                if output.is_borrowed() {
                    stats.step_outputs_borrowed += 1;
                } else {
                    stats.step_outputs_owned += 1;
                }

                level_parents += 1;
                let output_generated_count = output.generated_count();
                self.record_transitions(
                    usize::try_from(output_generated_count).unwrap_or(usize::MAX),
                );
                level_generated += u64::from(output_generated_count);

                if crosscheck_with_interpreter {
                    let parent_slice = crosscheck_parent.as_deref().ok_or_else(|| {
                        CheckResult::from_error(
                            RuntimeCheckError::Internal(
                                "compiled BFS interpreter crosscheck missing parent snapshot"
                                    .to_string(),
                            )
                            .into(),
                            self.stats.clone(),
                        )
                    });
                    let parent_slice = match parent_slice {
                        Ok(parent_slice) => parent_slice,
                        Err(result) => {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return result;
                        }
                    };
                    let compiled_successors = {
                        let mut successors = Vec::with_capacity(output.successor_count());
                        output
                            .for_each_successor(|successor| {
                                successors.push(successor.to_vec());
                                Ok::<(), std::convert::Infallible>(())
                            })
                            .expect("infallible compiled successor copy");
                        successors
                    };
                    let interpreter_actions = match self
                        .compiled_bfs_interpreter_action_successors_for_parent(
                            parent_slice,
                            &registry,
                        ) {
                        Ok(action_successors) => action_successors,
                        Err(result) => {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return result;
                        }
                    };
                    let interpreter_action_counts: Vec<_> = interpreter_actions
                        .iter()
                        .map(|action| {
                            (
                                action.action_idx,
                                action.action_name.as_str(),
                                action.successors.len(),
                            )
                        })
                        .collect();
                    let interpreter_generated: usize = interpreter_actions
                        .iter()
                        .map(|action| action.successors.len())
                        .sum();

                    let mut remaining_compiled =
                        std::collections::BTreeMap::<Vec<i64>, usize>::new();
                    for successor in &compiled_successors {
                        *remaining_compiled.entry(successor.clone()).or_insert(0) += 1;
                    }

                    let mut first_missing = None;
                    'actions: for action in &interpreter_actions {
                        for (successor_idx, successor) in action.successors.iter().enumerate() {
                            if let Some(count) = remaining_compiled.get_mut(successor) {
                                *count -= 1;
                                if *count == 0 {
                                    remaining_compiled.remove(successor);
                                }
                            } else {
                                first_missing = Some((
                                    action.action_idx,
                                    action.action_name.as_str(),
                                    successor_idx,
                                    successor.as_slice(),
                                ));
                                break 'actions;
                            }
                        }
                    }

                    if let Some((action_idx, action_name, successor_idx, missing_successor)) =
                        first_missing
                    {
                        eprintln!(
                            "[compiled-bfs-crosscheck] missing-edge depth={first_depth} parent={parent_idx}: action_idx={action_idx} action={action_name} action_successor_idx={successor_idx} compiled_generated={} compiled_returned={} interpreter_generated={} interpreter_action_counts={interpreter_action_counts:?} parent_flat={parent_slice:?} missing_successor_flat={missing_successor:?}",
                            output_generated_count,
                            compiled_successors.len(),
                            interpreter_generated,
                        );
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(
                                "compiled BFS interpreter crosscheck found a missing successor edge"
                                    .to_string(),
                            )
                            .into(),
                            self.stats.clone(),
                        );
                    }

                    if interpreter_generated != compiled_successors.len()
                        || !remaining_compiled.is_empty()
                    {
                        let first_extra = compiled_successors
                            .iter()
                            .find(|successor| remaining_compiled.contains_key(*successor));
                        eprintln!(
                            "[compiled-bfs-crosscheck] extra-edge depth={first_depth} parent={parent_idx}: compiled_generated={} compiled_returned={} interpreter_generated={} interpreter_action_counts={interpreter_action_counts:?} parent_flat={parent_slice:?} extra_successor_flat={first_extra:?}",
                            output_generated_count,
                            compiled_successors.len(),
                            interpreter_generated,
                        );
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(
                                "compiled BFS interpreter crosscheck found an extra compiled successor edge"
                                    .to_string(),
                            )
                            .into(),
                            self.stats.clone(),
                        );
                    }
                }

                let had_raw_successors = output_generated_count > 0;
                if had_raw_successors {
                    self.stats.max_depth = self.stats.max_depth.max(succ_depth);
                }

                // Handle invariant violation from compiled step.
                if !output.invariant_ok() {
                    let Some(inv_idx) = output.failed_invariant_idx() else {
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(
                                "compiled BFS reported invariant failure without failed invariant metadata"
                                    .to_string(),
                            )
                            .into(),
                            self.stats.clone(),
                        );
                    };
                    let inv_name = self
                        .config
                        .invariants
                        .get(inv_idx as usize)
                        .cloned()
                        .unwrap_or_else(|| format!("invariant_{inv_idx}"));

                    let Some(failed_succ_idx) = output.failed_successor_idx() else {
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(
                                "compiled BFS reported invariant failure without failed successor metadata"
                                    .to_string(),
                            )
                            .into(),
                            self.stats.clone(),
                        );
                    };

                    let Some(succ_slice) = output.successor_at(failed_succ_idx as usize) else {
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(format!(
                                "compiled BFS reported invariant failure successor index {failed_succ_idx} outside {} successors",
                                output.successor_count()
                            ))
                            .into(),
                            self.stats.clone(),
                        );
                    };

                    let state_result = self.try_reconstruct_state_from_flat(succ_slice, &registry);

                    flat_queue.advance_read_cursor(parent_idx + 1);
                    stats.parents_processed += level_parents;
                    stats.successors_generated += level_generated;
                    stats.successors_new += level_new;
                    let state = match state_result {
                        Ok(state) => state,
                        Err(result) => {
                            self.report_compiled_bfs_stats(&stats);
                            return result;
                        }
                    };
                    self.report_compiled_bfs_stats(&stats);

                    return CheckResult::InvariantViolation {
                        invariant: inv_name,
                        trace: Trace::from_states(vec![state]),
                        stats: self.stats.clone(),
                    };
                }

                // Process new successors: second-level dedup against global seen set.
                // Clone the bridge to avoid holding an immutable borrow on
                // `self.flat_bfs_adapter` while calling mutable methods below.
                // Part of #3986: Phase 3 zero-alloc compiled BFS.
                let bridge = self
                    .flat_bfs_adapter
                    .as_ref()
                    .map(|adapter| adapter.bridge().clone());
                let (parent_fp, parent_trace_loc) = match flat_queue.meta_at_offset(parent_idx) {
                    Some((fp, _depth, trace_loc)) => (fp, trace_loc),
                    None => {
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(
                            RuntimeCheckError::Internal(format!(
                                "compiled BFS missing parent metadata at index {parent_idx}",
                            ))
                            .into(),
                            self.stats.clone(),
                        );
                    }
                };
                let mut liveness_successors = self.liveness_cache.cache_for_liveness.then(Vec::new);

                let successor_result = output.for_each_successor(|flat_succ| {
                    if use_compiled_fingerprint {
                        let Some(bridge) = bridge.as_ref() else {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return Err(CheckResult::from_error(
                                RuntimeCheckError::Internal(
                                    "compiled BFS flat fingerprinting requested without \
                                     a FlatBfsAdapter"
                                        .to_string(),
                                )
                                .into(),
                                self.stats.clone(),
                            ));
                        };
                        if let Err(error) = bridge.validate_raw_buffer_slot_count(flat_succ) {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return Err(self.flat_reconstruction_error_result(
                                "failed to validate compiled BFS successor buffer",
                                error,
                            ));
                        }
                        if bridge.raw_admission_validation_required() {
                            if let Err(error) = bridge.validate_raw_buffer_for_admission(flat_succ)
                            {
                                flat_queue.advance_read_cursor(parent_idx + 1);
                                stats.parents_processed += level_parents;
                                stats.successors_generated += level_generated;
                                stats.successors_new += level_new;
                                self.report_compiled_bfs_stats(&stats);
                                return Err(self.flat_reconstruction_error_result(
                                    "failed to validate compiled BFS successor buffer",
                                    error,
                                ));
                            }
                        }
                    }

                    // Zero-allocation fast path: compute fingerprint directly
                    // from the raw &[i64] buffer without constructing FlatState
                    // (avoids Box<[i64]> heap allocation per successor).
                    // Part of #3986: Phase 3 zero-alloc compiled BFS.
                    // Part of #3987/#4356: Use the same fingerprint domain
                    // selected for queued init states. `flat_state_primary`
                    // can activate compiled-flat fingerprints even when
                    // `jit_compiled_fp_active` is false for fully-flat
                    // non-scalar layouts.
                    let succ_fp = if use_compiled_fingerprint {
                        super::super::invariants::fingerprint_flat_compiled(flat_succ)
                    } else {
                        let Some(bridge) = bridge.as_ref() else {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return Err(CheckResult::from_error(
                                RuntimeCheckError::Internal(
                                    "compiled BFS traditional fingerprinting requested without \
                                     a FlatBfsAdapter"
                                        .to_string(),
                                )
                                .into(),
                                self.stats.clone(),
                            ));
                        };
                        match bridge.try_traditional_fingerprint_from_buffer(flat_succ, &registry) {
                            Ok(fp) => fp,
                            Err(error) => {
                                flat_queue.advance_read_cursor(parent_idx + 1);
                                stats.parents_processed += level_parents;
                                stats.successors_generated += level_generated;
                                stats.successors_new += level_new;
                                self.report_compiled_bfs_stats(&stats);
                                return Err(self.flat_reconstruction_error_result(
                                    "failed to fingerprint compiled BFS successor buffer",
                                    error,
                                ));
                            }
                        }
                    };

                    if let Some(ref mut successors) = liveness_successors {
                        successors.push(succ_fp);
                    }

                    // Global dedup check.
                    match self.is_state_seen_checked(succ_fp) {
                        Ok(true) => return Ok(()), // Already seen globally
                        Ok(false) => {}            // New state
                        Err(result) => {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            self.report_compiled_bfs_stats(&stats);
                            return Err(result);
                        }
                    }

                    // Mark as seen in global set.
                    let previous_parent_trace_loc = self.trace.current_parent_trace_loc;
                    self.trace.current_parent_trace_loc = Some(parent_trace_loc);
                    let mark_result =
                        self.mark_state_seen_fp_only_checked(succ_fp, Some(parent_fp), succ_depth);
                    self.trace.current_parent_trace_loc = previous_parent_trace_loc;

                    match mark_result {
                        Ok(true) => {}              // Successfully inserted
                        Ok(false) => return Ok(()), // Race condition (shouldn't happen in sequential)
                        Err(result) => {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            self.report_compiled_bfs_stats(&stats);
                            return Err(result);
                        }
                    }

                    level_new += 1;
                    self.stats.max_depth = self.stats.max_depth.max(succ_depth);

                    // Get trace_loc from the last inserted state.
                    let trace_loc = self.trace.last_inserted_trace_loc;

                    // Zero-allocation enqueue: push raw buffer directly into
                    // the arena without constructing FlatState.
                    // Part of #3986: Phase 3 zero-alloc compiled BFS.
                    flat_queue.push_raw_buffer(flat_succ, succ_fp, succ_depth, trace_loc);
                    Ok(())
                });
                if let Err(result) = successor_result {
                    return result;
                }

                if let Some(successors) = liveness_successors {
                    if let Err(error) = self.liveness_cache.successors.insert(parent_fp, successors)
                    {
                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);
                        return CheckResult::from_error(error, self.stats.clone());
                    }
                }

                // Deadlock detection: if no successors were generated.
                if self.exploration.check_deadlock && !had_raw_successors {
                    let state_result = match flat_queue.remaining_state_at_offset(parent_idx) {
                        Some(parent_slice) => {
                            self.try_reconstruct_state_from_flat(parent_slice, &registry)
                        }
                        None => Err(CheckResult::from_error(
                            RuntimeCheckError::Internal(
                                "compiled BFS deadlock reported without a parent state".to_string(),
                            )
                            .into(),
                            self.stats.clone(),
                        )),
                    };
                    flat_queue.advance_read_cursor(parent_idx + 1);
                    stats.parents_processed += level_parents;
                    stats.successors_generated += level_generated;
                    stats.successors_new += level_new;
                    let state = match state_result {
                        Ok(state) => state,
                        Err(result) => {
                            self.report_compiled_bfs_stats(&stats);
                            return result;
                        }
                    };
                    self.report_compiled_bfs_stats(&stats);

                    return CheckResult::Deadlock {
                        trace: Trace::from_states(vec![state]),
                        stats: self.stats.clone(),
                    };
                }

                // Part of #4203: Update state_count after each parent so that
                // progress reporting, memory pressure checks, and state limit
                // checks see fresh data during level processing — not just at
                // level-end. This matches the per-dequeue update pattern in the
                // standard BFS worker loop (transport_seq.rs report_progress).
                self.stats.states_found = self.states_count();

                // Part of #4203: Periodic memory/progress check within the level.
                // Without this, memory pressure is only checked at level
                // boundaries, which can be arbitrarily far apart on wide
                // frontiers. Check every COMPILED_BFS_PROGRESS_INTERVAL parents.
                if level_parents % COMPILED_BFS_PROGRESS_INTERVAL == 0 {
                    if let Some(ref policy) = self.exploration.memory_policy {
                        use crate::memory::MemoryPressure;
                        if policy.check() == MemoryPressure::Critical {
                            let rss_mb = crate::memory::current_rss_bytes()
                                .map(|b| b / (1024 * 1024))
                                .unwrap_or(0);
                            let limit_mb = policy.limit_bytes() / (1024 * 1024);
                            eprintln!(
                                "[compiled-bfs] memory critical ({rss_mb} MB / {limit_mb} MB limit) \
                                 at parent {parent_idx} of level — stopping."
                            );
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            stats.successors_generated += level_generated;
                            stats.successors_new += level_new;
                            self.report_compiled_bfs_stats(&stats);
                            return CheckResult::LimitReached {
                                limit_type: super::super::LimitType::Memory,
                                stats: self.stats.clone(),
                            };
                        }
                    }
                }
            }

            // Advance past all parents we processed.
            flat_queue.advance_read_cursor(consumed_count);
            stats.parents_processed += level_parents;
            stats.successors_generated += level_generated;
            stats.successors_new += level_new;
            stats.levels_completed += 1;

            // Update model checker stats.
            let total_states = self.states_count();
            self.stats.states_found = total_states;

            // Progress reporting.
            if stats.levels_completed % 5 == 0 {
                eprintln!(
                    "[compiled-bfs] level {}: {} states, {} generated, {} new, queue={}",
                    stats.levels_completed,
                    total_states,
                    stats.successors_generated,
                    stats.successors_new,
                    flat_queue.len(),
                );
            }

            // Arena reset at level boundaries.
            crate::arena::worker_arena_reset();

            if early_break {
                break;
            }
        }

        self.report_compiled_bfs_stats(&stats);
        let result = self.finish_check_after_bfs(depth_limit_reached, false);

        // Publish verdict to portfolio/cooperative.
        if let Some(ref sv) = self.portfolio_verdict {
            let verdict = match &result {
                CheckResult::Success(_) => Verdict::Satisfied,
                CheckResult::InvariantViolation { .. }
                | CheckResult::PropertyViolation { .. }
                | CheckResult::LivenessViolation { .. } => Verdict::Violated,
                _ => Verdict::Unknown,
            };
            sv.publish(verdict);
        }
        #[cfg(feature = "z4")]
        if let Some(ref coop) = self.cooperative {
            let verdict = match &result {
                CheckResult::Success(_) => Verdict::Satisfied,
                CheckResult::InvariantViolation { .. }
                | CheckResult::PropertyViolation { .. }
                | CheckResult::LivenessViolation { .. } => Verdict::Violated,
                _ => Verdict::Unknown,
            };
            coop.verdict.publish(verdict);
            coop.mark_bfs_complete();
        }

        result
    }

    /// Check whether the compiled BFS level loop is eligible for this run.
    ///
    /// Part of #3988: JIT V2 Phase 5 compiled BFS step.
    /// Part of #4171: End-to-end compiled BFS wiring (config/env controls).
    #[must_use]
    fn compiled_bfs_level_eligible(&self) -> bool {
        // Force-disable via config or env var.
        if self.config.use_compiled_bfs == Some(false) {
            return false;
        }
        if crate::check::debug::compiled_bfs_disabled() {
            return false;
        }
        if !self.flat_state_primary {
            return false;
        }
        if self.compiled_bfs_step.is_none() && !self.fused_bfs_level_available() {
            return false;
        }
        if self.jit_monolithic_disabled {
            return false;
        }
        if !self.compiled.eval_implied_actions.is_empty() {
            return false;
        }
        if !self.config.action_constraints.is_empty() {
            return false;
        }
        if !self.config.constraints.is_empty() && !self.fused_bfs_level_available() {
            return false;
        }
        if self.por.independence.is_some() {
            return false;
        }
        if self.coverage.collect && !self.coverage.actions.is_empty() {
            return false;
        }
        if !self.config.trace_invariants.is_empty() {
            return false;
        }
        if !self.symmetry.perms.is_empty() {
            return false;
        }
        if self.compiled.cached_view_name.is_some() {
            return false;
        }
        if self.inline_liveness_active() {
            return false;
        }
        true
    }

    /// Whether the fused BFS level function is available and should be used.
    ///
    /// The fused path processes entire frontiers in a single native call,
    /// eliminating per-parent Rust-to-JIT boundary crossings. Falls back to
    /// the per-parent `CompiledBfsStep` path when unavailable.
    ///
    /// Part of #4171: End-to-end compiled BFS wiring.
    #[must_use]
    fn fused_bfs_level_available(&self) -> bool {
        if !self.config.trace_invariants.is_empty() {
            return false;
        }
        self.compiled_bfs_level
            .as_ref()
            .is_some_and(|level| level.has_fused_level())
    }

    /// Whether the fused BFS level is backed by a native generated parent loop.
    #[must_use]
    fn native_fused_bfs_level_available(&self) -> bool {
        if !self.config.trace_invariants.is_empty() {
            return false;
        }
        self.compiled_bfs_level
            .as_ref()
            .is_some_and(|level| level.has_native_fused_level())
    }

    /// Whether the per-parent compiled step can be used without corrupting
    /// liveness state-graph capture in the current checker mode.
    #[must_use]
    fn compiled_bfs_step_usable_for_current_graph_mode(&self) -> bool {
        if !self.config.constraints.is_empty() {
            return false;
        }
        self.compiled_bfs_step.as_ref().is_some_and(|step| {
            !self.liveness_cache.cache_for_liveness || step.preserves_state_graph_successor_edges()
        })
    }

    fn disable_compiled_bfs_for_standard_fallback(&mut self) {
        self.compiled_bfs_level = None;
        self.compiled_bfs_step = None;
    }

    #[must_use]
    fn llvm2_native_fused_strict_enabled(&self) -> bool {
        crate::check::debug::llvm2_native_fused_strict()
    }

    fn strict_native_fused_fallback_result(&self, reason: impl std::fmt::Display) -> CheckResult {
        CheckResult::from_error(
            RuntimeCheckError::Internal(format!(
                "strict LLVM2 native fused requirement failed: {reason}"
            ))
            .into(),
            self.stats.clone(),
        )
    }

    /// Reconstruct a TLA+ `State` from a flat i64 buffer.
    ///
    /// Uses the `FlatBfsAdapter` to convert flat -> ArrayState -> State.
    /// This is the cold path used only for error reporting (invariant
    /// violations, deadlock).
    ///
    /// Part of #3988.
    fn flat_reconstruction_error_result(
        &self,
        context: &str,
        error: impl std::fmt::Display,
    ) -> CheckResult {
        CheckResult::from_error(
            RuntimeCheckError::Internal(format!("{context}: {error}")).into(),
            self.stats.clone(),
        )
    }

    fn record_fp_only_batch_admission_bookkeeping(
        &mut self,
        fp: Fingerprint,
        parent: Option<Fingerprint>,
        parent_trace_loc: Option<u64>,
        depth: usize,
    ) -> Result<u64, CheckResult> {
        debug_assert!(!self.state_storage.store_full_states);

        if let Some(ref mut trace_file) = self.trace.trace_file {
            let loc = if let Some(parent_fp) = parent {
                let parent_loc = if let Some(cached) = parent_trace_loc {
                    cached
                } else {
                    match self.trace.trace_locs.get(&parent_fp) {
                        Some(loc) => loc,
                        None => {
                            return Err(CheckResult::from_error(
                                RuntimeCheckError::Internal(format!(
                                    "compiled BFS batch trace provenance missing parent trace location for {parent_fp:?}"
                                ))
                                .into(),
                                self.stats.clone(),
                            ));
                        }
                    }
                };
                match trace_file.write_state(parent_loc, fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            } else {
                match trace_file.write_initial(fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            };

            if let Some(loc) = loc {
                self.trace.last_inserted_trace_loc = loc;
                if !self.trace.lazy_trace_index && !self.trace.trace_locs.insert(fp, loc) {
                    self.trace.trace_degraded = true;
                }
            }
        }

        if self.checkpoint.dir.is_some() {
            self.trace.depths.insert(fp, depth);
        }

        Ok(self.trace.last_inserted_trace_loc)
    }

    fn try_reconstruct_state_from_flat(
        &self,
        flat_buf: &[i64],
        registry: &crate::var_index::VarRegistry,
    ) -> Result<crate::State, CheckResult> {
        self.try_reconstruct_array_state_from_flat(flat_buf, registry)
            .map(|array| array.to_state(registry))
    }

    fn try_reconstruct_array_state_from_flat(
        &self,
        flat_buf: &[i64],
        registry: &crate::var_index::VarRegistry,
    ) -> Result<crate::state::ArrayState, CheckResult> {
        if let Some(ref adapter) = self.flat_bfs_adapter {
            adapter
                .bridge()
                .try_to_array_state_from_buffer(flat_buf, registry)
                .map_err(|error| {
                    self.flat_reconstruction_error_result(
                        "failed to reconstruct compiled BFS flat buffer",
                        error,
                    )
                })
        } else {
            // Fallback: treat each i64 as SmallInt.
            let values: Vec<_> = flat_buf
                .iter()
                .map(|&v| crate::Value::SmallInt(v))
                .collect();
            Ok(crate::state::ArrayState::from_values(values))
        }
    }

    /// Report compiled BFS loop statistics.
    fn report_compiled_bfs_stats(&self, stats: &CompiledBfsLoopStats) {
        let execution = stats
            .execution_started_at
            .map(|started_at| started_at.elapsed());
        let execution_nanos = execution
            .map(|duration| duration.as_nanos())
            .unwrap_or_default();
        let execution_seconds = execution
            .map(|duration| duration.as_secs_f64())
            .unwrap_or_default();
        eprintln!(
            "[compiled-bfs] completed: {} levels, {} parents, {} generated, {} new, {} total states, step_outputs_borrowed={}, step_outputs_owned={}, fused_pre_seen_lookups={}, fused_pre_seen_skipped={}, fused_admission_validations_elided={}, execution_time_ns={}, execution_time_seconds={:.6}",
            stats.levels_completed,
            stats.parents_processed,
            stats.successors_generated,
            stats.successors_new,
            self.states_count(),
            stats.step_outputs_borrowed,
            stats.step_outputs_owned,
            stats.fused_pre_seen_lookups,
            stats.fused_pre_seen_lookups_skipped,
            stats.fused_admission_validations_elided,
            execution_nanos,
            execution_seconds,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{
        fused_successor_needs_pre_seen_lookup, fused_successor_needs_rust_regular_invariant_check,
    };
    use crate::arena::BulkStateStorage;
    use crate::check::model_checker::bfs::compiled_step_trait::{
        CompiledBfsLevel, CompiledBfsStep, CompiledLevelResult,
    };
    use crate::check::model_checker::bfs::flat_frontier::FlatBfsFrontier;
    use crate::check::model_checker::bfs::storage_modes::FingerprintOnlyStorage;
    use crate::check::model_checker::frontier::BfsFrontier;
    use crate::check::model_checker::{CheckResult, ModelChecker};
    use crate::config::Config;
    use crate::state::{Fingerprint, StateLayout, VarLayoutKind};
    #[cfg(feature = "llvm2")]
    use crate::storage::{CapacityStatus, InsertOutcome, LookupOutcome};
    use crate::storage::{FingerprintSet, FingerprintStorage};
    use crate::test_support::parse_module;
    use crate::{CheckError, InfraCheckError, TraceFile};
    #[cfg(feature = "llvm2")]
    use std::collections::HashSet;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;
    #[cfg(feature = "llvm2")]
    use std::sync::Mutex;
    use tla_jit_runtime::{BfsStepError, FlatBfsStepOutput};

    fn two_parent_liveness_module() -> tla_core::ast::Module {
        parse_module(
            r#"
---- MODULE CompiledBfsLivenessTwoParentTest ----
VARIABLE x
Init == x = 0 \/ x = 1
Next == \/ /\ x = 0 /\ x' = 2
        \/ /\ x = 1 /\ x' = 2
Inv == TRUE
====
"#,
        )
    }

    fn seed_two_parent_flat_frontier(
        checker: &mut ModelChecker<'_>,
    ) -> (
        FlatBfsFrontier,
        FingerprintOnlyStorage,
        Fingerprint,
        Fingerprint,
    ) {
        checker.trace.cached_next_name = Some("Next".to_string());
        checker.trace.cached_resolved_next_name = Some("Next".to_string());

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));

        let fp0 = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        let fp1 = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[1]);
        checker
            .mark_state_seen_fp_only_checked(fp0, None, 0)
            .expect("seed x=0");
        checker
            .mark_state_seen_fp_only_checked(fp1, None, 0)
            .expect("seed x=1");

        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], fp0, 0, 0);
        flat_queue.push_raw_buffer(&[1], fp1, 0, 0);

        let storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            checker.ctx.var_registry().len(),
        );
        (flat_queue, storage, fp0, fp1)
    }

    fn assert_both_parent_liveness_edges(
        checker: &ModelChecker<'_>,
        fp0: Fingerprint,
        fp1: Fingerprint,
    ) {
        let graph = checker
            .liveness_cache
            .successors
            .as_inner_map()
            .expect("test uses in-memory successor graph");
        let s0 = graph.get(&fp0).expect("x=0 liveness parent entry");
        let s1 = graph.get(&fp1).expect("x=1 liveness parent entry");

        assert_eq!(s0.len(), 1, "x=0 should retain its edge to x=2");
        assert_eq!(s1.len(), 1, "x=1 duplicate child edge must not be lost");
        assert_eq!(s0[0], s1[0], "both parents should point at x=2");
    }

    struct DuplicateOnlyFusedLevel;

    impl CompiledBfsLevel for DuplicateOnlyFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 1);
            Some(Ok(CompiledLevelResult::from_successor_arena(
                vec![],
                0,
                1,
                1,
                1,
                0,
                true,
                None,
                None,
                None,
                true,
            )))
        }
    }

    struct DuplicateSuccessorFusedLevel;

    impl CompiledBfsLevel for DuplicateSuccessorFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 1);
            Some(Ok(
                CompiledLevelResult::from_successor_arena_with_parent_indices(
                    vec![0],
                    Some(vec![0]),
                    1,
                    1,
                    1,
                    1,
                    1,
                    true,
                    None,
                    None,
                    None,
                    true,
                ),
            ))
        }
    }

    struct ShortSuccessfulFusedLevel;

    impl CompiledBfsLevel for ShortSuccessfulFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 2);
            Some(Ok(
                CompiledLevelResult::from_successor_arena_with_parent_indices(
                    vec![],
                    Some(Vec::new()),
                    0,
                    1,
                    1,
                    0,
                    0,
                    true,
                    None,
                    None,
                    None,
                    true,
                ),
            ))
        }
    }

    #[cfg(feature = "llvm2")]
    struct CompleteDeadlockMetadataFusedLevel;

    #[cfg(feature = "llvm2")]
    impl CompiledBfsLevel for CompleteDeadlockMetadataFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 2);
            let mut arena = tla_llvm2::Llvm2SuccessorArena::with_capacity(1, 1);
            let mut abi = arena.prepare_abi(1).expect("prepare LLVM2 arena ABI");
            unsafe {
                *abi.states = 2;
                *abi.parent_index = 1;
                *abi.fingerprints =
                    crate::check::model_checker::invariants::fingerprint_flat_compiled(&[2]).0;
            }
            abi.state_count = 1;
            abi.generated = 1;
            abi.parents_processed = 2;
            abi.first_zero_generated_parent_idx = 0;
            abi.raw_successor_metadata_complete = 1;
            let outcome = unsafe { arena.commit_abi(&abi) }.expect("commit LLVM2 arena ABI");

            Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                arena,
                outcome.parents_processed,
                outcome.total_generated,
                outcome.total_new,
                outcome.invariant.is_ok(),
                None,
                None,
                None,
                true,
            )))
        }
    }

    #[cfg(feature = "llvm2")]
    struct ZeroGeneratedDeadlockMetadataFusedLevel {
        first_zero_generated_parent_idx: u32,
    }

    #[cfg(feature = "llvm2")]
    impl CompiledBfsLevel for ZeroGeneratedDeadlockMetadataFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 2);
            let mut arena = tla_llvm2::Llvm2SuccessorArena::with_capacity(1, 0);
            let mut abi = arena.prepare_abi(0).expect("prepare empty LLVM2 arena ABI");
            abi.state_count = 0;
            abi.generated = 0;
            abi.parents_processed = 2;
            abi.first_zero_generated_parent_idx = self.first_zero_generated_parent_idx;
            abi.raw_successor_metadata_complete = 1;
            let outcome = unsafe { arena.commit_abi(&abi) }.expect("commit empty LLVM2 arena ABI");

            Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                arena,
                outcome.parents_processed,
                outcome.total_generated,
                outcome.total_new,
                outcome.invariant.is_ok(),
                None,
                None,
                None,
                true,
            )))
        }
    }

    struct MalformedInvariantFusedLevel;

    impl CompiledBfsLevel for MalformedInvariantFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 2);
            Some(Ok(CompiledLevelResult::from_successor_arena(
                vec![],
                0,
                1,
                1,
                0,
                0,
                false,
                Some(1),
                Some(0),
                None,
                true,
            )))
        }
    }

    struct BatchAdmissionFusedLevel {
        calls: std::sync::atomic::AtomicUsize,
    }

    impl CompiledBfsLevel for BatchAdmissionFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            let call = self.calls.fetch_add(1, Ordering::SeqCst);
            if call == 0 {
                assert_eq!(parent_count, 1);
                Some(Ok(
                    CompiledLevelResult::from_successor_arena_with_parent_indices(
                        vec![1, 2],
                        Some(vec![0, 0]),
                        2,
                        1,
                        1,
                        2,
                        2,
                        true,
                        None,
                        None,
                        None,
                        true,
                    ),
                ))
            } else {
                Some(Ok(
                    CompiledLevelResult::from_successor_arena_with_parent_indices(
                        vec![],
                        Some(Vec::new()),
                        0,
                        1,
                        parent_count,
                        0,
                        0,
                        true,
                        None,
                        None,
                        None,
                        true,
                    ),
                ))
            }
        }
    }

    #[cfg(feature = "llvm2")]
    struct Llvm2BorrowedBatchAdmissionFusedLevel {
        calls: AtomicUsize,
    }

    #[cfg(feature = "llvm2")]
    impl CompiledBfsLevel for Llvm2BorrowedBatchAdmissionFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            let call = self.calls.fetch_add(1, Ordering::SeqCst);
            let mut arena = tla_llvm2::Llvm2SuccessorArena::new(1);
            if call == 0 {
                assert_eq!(parent_count, 1);
                arena.push_successor(0, &[1]).unwrap();
                arena.push_successor(0, &[2]).unwrap();
                Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                    arena, 1, 2, 2, true, None, None, None, true,
                )))
            } else {
                Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                    arena,
                    parent_count,
                    0,
                    0,
                    true,
                    None,
                    None,
                    None,
                    true,
                )))
            }
        }
    }

    #[cfg(feature = "llvm2")]
    struct Llvm2BorrowedBatchStorageFaultFusedLevel;

    #[cfg(feature = "llvm2")]
    impl CompiledBfsLevel for Llvm2BorrowedBatchStorageFaultFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            assert_eq!(parent_count, 1);
            let mut arena = tla_llvm2::Llvm2SuccessorArena::new(1);
            arena.push_successor(0, &[1]).unwrap();
            arena.push_successor(0, &[2]).unwrap();
            arena.push_successor(0, &[3]).unwrap();
            arena.push_successor(0, &[4]).unwrap();
            Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                arena, 1, 4, 4, true, None, None, None, true,
            )))
        }
    }

    #[cfg(feature = "llvm2")]
    struct Llvm2BorrowedBatchTraceProvenanceFusedLevel {
        calls: AtomicUsize,
    }

    #[cfg(feature = "llvm2")]
    impl CompiledBfsLevel for Llvm2BorrowedBatchTraceProvenanceFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            let call = self.calls.fetch_add(1, Ordering::SeqCst);
            let mut arena = tla_llvm2::Llvm2SuccessorArena::new(1);
            if call == 0 {
                assert_eq!(parent_count, 2);
                arena.push_successor(0, &[10]).unwrap();
                arena.push_successor(1, &[20]).unwrap();
                Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                    arena, 2, 2, 2, true, None, None, None, true,
                )))
            } else {
                Some(Ok(CompiledLevelResult::from_llvm2_successor_arena(
                    arena,
                    parent_count,
                    0,
                    0,
                    true,
                    None,
                    None,
                    None,
                    true,
                )))
            }
        }
    }

    #[cfg(feature = "llvm2")]
    struct BorrowedBatchOnlyFingerprintSet {
        seen: Mutex<HashSet<Fingerprint>>,
        value_batch_calls: AtomicUsize,
        scratch_ptr: AtomicUsize,
        scratch_reused_calls: AtomicUsize,
        fault_at_value_batch_index: Option<usize>,
        dropped: AtomicUsize,
    }

    #[cfg(feature = "llvm2")]
    impl BorrowedBatchOnlyFingerprintSet {
        fn new() -> Self {
            Self {
                seen: Mutex::new(HashSet::new()),
                value_batch_calls: AtomicUsize::new(0),
                scratch_ptr: AtomicUsize::new(0),
                scratch_reused_calls: AtomicUsize::new(0),
                fault_at_value_batch_index: None,
                dropped: AtomicUsize::new(0),
            }
        }

        fn with_fault_at_value_batch_index(index: usize) -> Self {
            Self {
                fault_at_value_batch_index: Some(index),
                ..Self::new()
            }
        }

        fn insert_one(&self, fp: Fingerprint) -> InsertOutcome {
            if self.seen.lock().unwrap().insert(fp) {
                InsertOutcome::Inserted
            } else {
                InsertOutcome::AlreadyPresent
            }
        }
    }

    #[cfg(feature = "llvm2")]
    impl tla_mc_core::FingerprintSet<Fingerprint> for BorrowedBatchOnlyFingerprintSet {
        fn insert_checked(&self, fingerprint: Fingerprint) -> InsertOutcome {
            self.insert_one(fingerprint)
        }

        fn contains_checked(&self, fingerprint: Fingerprint) -> LookupOutcome {
            if self.seen.lock().unwrap().contains(&fingerprint) {
                LookupOutcome::Present
            } else {
                LookupOutcome::Absent
            }
        }

        fn len(&self) -> usize {
            self.seen.lock().unwrap().len()
        }

        fn has_errors(&self) -> bool {
            self.dropped.load(Ordering::SeqCst) > 0
        }

        fn dropped_count(&self) -> usize {
            self.dropped.load(Ordering::SeqCst)
        }

        fn capacity_status(&self) -> CapacityStatus {
            CapacityStatus::Normal
        }
    }

    #[cfg(feature = "llvm2")]
    impl FingerprintSet for BorrowedBatchOnlyFingerprintSet {
        fn insert_batch_checked(&self, _fingerprints: &[Fingerprint]) -> Vec<InsertOutcome> {
            panic!("borrowed LLVM2 batch admission should not stage Fingerprint values")
        }

        fn insert_batch_fingerprint_values_checked(
            &self,
            _fingerprint_values: &[u64],
        ) -> Vec<InsertOutcome> {
            panic!("borrowed LLVM2 batch admission should use caller-owned outcome scratch")
        }

        fn insert_batch_fingerprint_values_checked_into(
            &self,
            fingerprint_values: &[u64],
            outcomes: &mut Vec<InsertOutcome>,
        ) {
            self.value_batch_calls.fetch_add(1, Ordering::SeqCst);
            outcomes.clear();
            outcomes.reserve(fingerprint_values.len());
            for (idx, fp) in fingerprint_values.iter().enumerate() {
                if self.fault_at_value_batch_index == Some(idx) {
                    self.dropped.fetch_add(1, Ordering::SeqCst);
                    outcomes.push(InsertOutcome::StorageFault(
                        crate::storage::StorageFault::new(
                            "borrowed_llvm2_test",
                            "insert_batch_fingerprint_values_checked_into",
                            "synthetic prefix fault",
                        ),
                    ));
                    break;
                }
                outcomes.push(self.insert_one(Fingerprint(*fp)));
            }

            let ptr = outcomes.as_ptr() as usize;
            let previous = self.scratch_ptr.load(Ordering::SeqCst);
            if previous == 0 {
                self.scratch_ptr.store(ptr, Ordering::SeqCst);
            } else if previous == ptr {
                self.scratch_reused_calls.fetch_add(1, Ordering::SeqCst);
            } else {
                panic!("borrowed LLVM2 batch admission replaced outcome scratch allocation");
            }
        }
    }

    struct MixedBatchAdmissionFusedLevel {
        calls: AtomicUsize,
    }

    impl CompiledBfsLevel for MixedBatchAdmissionFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            let call = self.calls.fetch_add(1, Ordering::SeqCst);
            if call == 0 {
                assert_eq!(arena, &[0]);
                assert_eq!(parent_count, 1);
                Some(Ok(
                    CompiledLevelResult::from_successor_arena_with_parent_indices(
                        vec![1, 2],
                        Some(vec![0, 0]),
                        2,
                        1,
                        1,
                        2,
                        2,
                        true,
                        None,
                        None,
                        None,
                        true,
                    ),
                ))
            } else {
                assert_eq!(arena, &[2]);
                assert_eq!(parent_count, 1);
                Some(Ok(
                    CompiledLevelResult::from_successor_arena_with_parent_indices(
                        vec![],
                        Some(Vec::new()),
                        0,
                        1,
                        parent_count,
                        0,
                        0,
                        true,
                        None,
                        None,
                        None,
                        true,
                    ),
                ))
            }
        }
    }

    struct BatchAdmissionMissingParentMetadataFusedLevel {
        calls: AtomicUsize,
    }

    impl CompiledBfsLevel for BatchAdmissionMissingParentMetadataFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            let call = self.calls.fetch_add(1, Ordering::SeqCst);
            if call == 0 {
                assert_eq!(parent_count, 1);
                Some(Ok(CompiledLevelResult::from_successor_arena(
                    vec![1],
                    1,
                    1,
                    1,
                    1,
                    1,
                    true,
                    None,
                    None,
                    None,
                    true,
                )))
            } else {
                Some(Ok(CompiledLevelResult::from_successor_arena(
                    vec![],
                    0,
                    1,
                    parent_count,
                    0,
                    0,
                    true,
                    None,
                    None,
                    None,
                    true,
                )))
            }
        }
    }

    struct NonBatchOutOfRangeParentAfterAppendFusedLevel;

    impl CompiledBfsLevel for NonBatchOutOfRangeParentAfterAppendFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            if parent_count == 1 {
                Some(Ok(
                    CompiledLevelResult::from_successor_arena_with_parent_indices(
                        vec![1, 2],
                        Some(vec![0, 1]),
                        2,
                        1,
                        1,
                        2,
                        2,
                        true,
                        None,
                        None,
                        None,
                        false,
                    ),
                ))
            } else {
                Some(Ok(
                    CompiledLevelResult::from_successor_arena_with_parent_indices(
                        vec![],
                        Some(Vec::new()),
                        0,
                        1,
                        parent_count,
                        0,
                        0,
                        true,
                        None,
                        None,
                        None,
                        false,
                    ),
                ))
            }
        }
    }

    struct BufferOverflowFusedLevel;

    impl CompiledBfsLevel for BufferOverflowFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            _parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            Some(Err(BfsStepError::BufferOverflow { partial_count: 0 }))
        }
    }

    struct CountingCompiledStep {
        calls: Arc<AtomicUsize>,
    }

    impl CompiledBfsStep for CountingCompiledStep {
        fn state_len(&self) -> usize {
            1
        }

        fn preserves_state_graph_successor_edges(&self) -> bool {
            true
        }

        fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            let successors = if state == [0] { vec![1] } else { vec![] };
            let successor_count = successors.len();
            Ok(FlatBfsStepOutput::from_parts(
                successors,
                1,
                successor_count,
                successor_count as u32,
                true,
                None,
                None,
            ))
        }
    }

    struct CompleteTwoParentCompiledStep {
        calls: Arc<AtomicUsize>,
    }

    impl CompiledBfsStep for CompleteTwoParentCompiledStep {
        fn state_len(&self) -> usize {
            1
        }

        fn preserves_state_graph_successor_edges(&self) -> bool {
            true
        }

        fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            let (successors, generated) = match state {
                [0] | [1] => (vec![2], 1),
                _ => (Vec::new(), 0),
            };
            Ok(FlatBfsStepOutput::from_parts(
                successors,
                1,
                generated,
                generated as u32,
                true,
                None,
                None,
            ))
        }
    }

    struct UnsafeLocalDedupFusedLevel {
        calls: Arc<AtomicUsize>,
    }

    impl CompiledBfsLevel for UnsafeLocalDedupFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            let result = if parent_count == 2 {
                CompiledLevelResult::from_successor_arena_with_parent_indices(
                    vec![2],
                    Some(vec![0]),
                    1,
                    1,
                    2,
                    2,
                    1,
                    true,
                    None,
                    None,
                    None,
                    true,
                )
                .with_state_graph_successors_complete(true)
            } else {
                CompiledLevelResult::from_successor_arena_with_parent_indices(
                    vec![],
                    Some(vec![]),
                    0,
                    1,
                    parent_count,
                    0,
                    0,
                    true,
                    None,
                    None,
                    None,
                    true,
                )
                .with_state_graph_successors_complete(true)
            };
            Some(Ok(result))
        }
    }

    struct UnsafeDedupingCompiledStep {
        calls: Arc<AtomicUsize>,
    }

    impl CompiledBfsStep for UnsafeDedupingCompiledStep {
        fn state_len(&self) -> usize {
            1
        }

        fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            match state {
                [0] => Ok(FlatBfsStepOutput::from_parts(
                    vec![2],
                    1,
                    1,
                    1,
                    true,
                    None,
                    None,
                )),
                [1] => Ok(FlatBfsStepOutput::from_parts(
                    vec![],
                    1,
                    0,
                    1,
                    true,
                    None,
                    None,
                )),
                _ => Ok(FlatBfsStepOutput::from_parts(
                    vec![],
                    1,
                    0,
                    0,
                    true,
                    None,
                    None,
                )),
            }
        }
    }

    struct FatalFusedLevel;

    impl CompiledBfsLevel for FatalFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            _parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            Some(Err(BfsStepError::FatalRuntimeError))
        }
    }

    struct TraceProvenanceCompiledStep;

    impl CompiledBfsStep for TraceProvenanceCompiledStep {
        fn state_len(&self) -> usize {
            1
        }

        fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
            let successors = match state {
                [0] => vec![10],
                [1] => vec![20],
                _ => Vec::new(),
            };
            let successor_count = successors.len();
            Ok(FlatBfsStepOutput::from_parts(
                successors,
                1,
                successor_count,
                successor_count as u32,
                true,
                None,
                None,
            ))
        }
    }

    struct PreflightFatalFusedLevel {
        preflight_seen: Arc<AtomicBool>,
        run_called: Arc<AtomicBool>,
    }

    impl CompiledBfsLevel for PreflightFatalFusedLevel {
        fn has_fused_level(&self) -> bool {
            true
        }

        fn preflight_fused_arena(
            &self,
            arena: &[i64],
            parent_count: usize,
        ) -> Result<(), BfsStepError> {
            assert_eq!(arena, &[0]);
            assert_eq!(parent_count, 1);
            self.preflight_seen.store(true, Ordering::SeqCst);
            Err(BfsStepError::FatalRuntimeError)
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            _parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            self.run_called.store(true, Ordering::SeqCst);
            Some(Err(BfsStepError::RuntimeError))
        }
    }

    #[test]
    fn compiled_bfs_fused_batch_admission_enqueues_new_successors() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsBatchAdmissionTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(BatchAdmissionFusedLevel {
            calls: std::sync::atomic::AtomicUsize::new(0),
        }));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 2);
                assert_eq!(stats.max_depth, 1);
                assert_eq!(stats.states_found, 2);
            }
            other => panic!("expected batch-admission fused level success, got {other:?}"),
        }
        assert_eq!(checker.test_seen_fps_len(), 2);
        assert_eq!(flat_queue.len(), 0);
        assert_eq!(flat_queue.flat_pushed(), 3);
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn compiled_bfs_fused_batch_admission_uses_borrowed_llvm2_sidecars() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsBorrowedBatchAdmissionTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(Llvm2BorrowedBatchAdmissionFusedLevel {
            calls: AtomicUsize::new(0),
        }));
        checker.compiled_bfs_step = None;

        let seen = Arc::new(BorrowedBatchOnlyFingerprintSet::new());
        checker.set_fingerprint_storage(seen.clone() as Arc<dyn FingerprintSet>);

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 2);
                assert_eq!(stats.max_depth, 1);
                assert_eq!(stats.states_found, 2);
            }
            other => panic!("expected borrowed batch-admission fused level success, got {other:?}"),
        }
        assert!(
            seen.value_batch_calls.load(Ordering::SeqCst) > 0,
            "borrowed LLVM2 sidecar batch path should call raw fingerprint admission"
        );
        assert!(
            seen.scratch_reused_calls.load(Ordering::SeqCst) > 0,
            "borrowed LLVM2 sidecar batch path should reuse caller-owned outcome scratch across levels"
        );
        assert_eq!(checker.test_seen_fps_len(), 2);
        assert_eq!(flat_queue.len(), 0);
        assert_eq!(flat_queue.flat_pushed(), 3);
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn compiled_bfs_borrowed_llvm2_batch_admission_preserves_inserted_prefix_on_storage_fault() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsBorrowedBatchAdmissionPrefixFaultTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(Llvm2BorrowedBatchStorageFaultFusedLevel));
        checker.compiled_bfs_step = None;

        let seen = Arc::new(BorrowedBatchOnlyFingerprintSet::with_fault_at_value_batch_index(3));
        checker.set_fingerprint_storage(seen.clone() as Arc<dyn FingerprintSet>);

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        let parent_fp = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        checker
            .mark_state_seen_fp_only_checked(parent_fp, None, 0)
            .expect("seed parent fingerprint");
        let duplicate_fp = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[2]);
        checker
            .mark_state_seen_fp_only_checked(duplicate_fp, None, 1)
            .expect("seed duplicate successor fingerprint");
        flat_queue.push_raw_buffer(&[0], parent_fp, 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error {
                error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, detail }),
                stats,
                ..
            } => {
                assert_eq!(dropped, 1);
                assert!(
                    detail.contains("synthetic prefix fault"),
                    "storage fault detail should be preserved, got: {detail}"
                );
                assert_eq!(stats.states_found, checker.test_seen_fps_len());
                assert_eq!(stats.states_found, 4);
            }
            other => panic!("expected borrowed LLVM2 prefix storage fault, got {other:?}"),
        }

        assert_eq!(
            seen.value_batch_calls.load(Ordering::SeqCst),
            1,
            "borrowed LLVM2 path should use raw fingerprint batch admission"
        );
        assert_eq!(checker.test_seen_fps_len(), 4);
        assert_eq!(flat_queue.len(), 2);
        assert_eq!(flat_queue.flat_pushed(), 3);
        let (remaining, count) = flat_queue
            .remaining_arena()
            .expect("inserted prefix should remain queued after storage fault");
        assert_eq!(count, 2);
        assert_eq!(remaining, &[1, 3]);
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn compiled_bfs_borrowed_llvm2_batch_admission_records_parent_trace_provenance() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.set_trace_file(TraceFile::create_temp().expect("trace file should initialize"));
        checker.compiled_bfs_level = Some(Box::new(Llvm2BorrowedBatchTraceProvenanceFusedLevel {
            calls: AtomicUsize::new(0),
        }));
        checker.compiled_bfs_step = None;

        let seen = Arc::new(BorrowedBatchOnlyFingerprintSet::new());
        checker.set_fingerprint_storage(seen.clone() as Arc<dyn FingerprintSet>);

        checker.trace.cached_next_name = Some("Next".to_string());
        checker.trace.cached_resolved_next_name = Some("Next".to_string());
        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));

        let fp0 = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        checker
            .mark_state_seen_fp_only_checked(fp0, None, 0)
            .expect("seed x=0");
        let loc0 = checker.trace.last_inserted_trace_loc;
        let fp1 = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[1]);
        checker
            .mark_state_seen_fp_only_checked(fp1, None, 0)
            .expect("seed x=1");
        let loc1 = checker.trace.last_inserted_trace_loc;

        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], fp0, 0, loc0);
        flat_queue.push_raw_buffer(&[1], fp1, 0, loc1);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            checker.ctx.var_registry().len(),
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        assert!(matches!(result, CheckResult::Success(_)), "got {result:?}");
        assert!(
            seen.value_batch_calls.load(Ordering::SeqCst) > 0,
            "borrowed LLVM2 path should use raw fingerprint batch admission"
        );
        let successor_10_fp =
            crate::check::model_checker::invariants::fingerprint_flat_compiled(&[10]);
        let successor_20_fp =
            crate::check::model_checker::invariants::fingerprint_flat_compiled(&[20]);
        let parents = checker
            .trace
            .trace_file
            .as_mut()
            .expect("trace file still installed")
            .build_parents_map()
            .expect("parents map should scan");
        assert_eq!(parents.get(&successor_10_fp), Some(&fp0));
        assert_eq!(parents.get(&successor_20_fp), Some(&fp1));
    }

    #[test]
    fn compiled_bfs_fused_batch_admission_skips_already_present_and_enqueues_later_inserted() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsBatchAdmissionMixedTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(MixedBatchAdmissionFusedLevel {
            calls: AtomicUsize::new(0),
        }));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        let parent_fp = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        flat_queue.push_raw_buffer(&[0], parent_fp, 0, 0);
        checker
            .mark_state_seen_fp_only_checked(parent_fp, None, 0)
            .expect("seed parent fingerprint");
        let duplicate_fp = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[1]);
        checker
            .mark_state_seen_fp_only_checked(duplicate_fp, None, 1)
            .expect("seed duplicate successor fingerprint");
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 2);
                assert_eq!(stats.max_depth, 1);
                assert_eq!(stats.states_found, 3);
            }
            other => panic!("expected mixed batch-admission fused level success, got {other:?}"),
        }
        assert_eq!(checker.test_seen_fps_len(), 3);
        assert_eq!(flat_queue.len(), 0);
        assert_eq!(flat_queue.flat_pushed(), 2);
    }

    #[test]
    fn compiled_bfs_fused_batch_admission_enqueues_inserted_prefix_before_storage_fault() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsBatchAdmissionPrefixFaultTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(BatchAdmissionFusedLevel {
            calls: std::sync::atomic::AtomicUsize::new(0),
        }));
        checker.compiled_bfs_step = None;
        let storage = FingerprintStorage::mmap(2, None)
            .expect("test mmap fingerprint storage should initialize");
        checker.set_fingerprint_storage(Arc::new(storage) as Arc<dyn FingerprintSet>);

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        let parent_fp = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        flat_queue.push_raw_buffer(&[0], parent_fp, 0, 0);
        checker
            .mark_state_seen_fp_only_checked(parent_fp, None, 0)
            .expect("seed parent fingerprint");
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error {
                error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
                stats,
                ..
            } => {
                assert_eq!(dropped, 1);
                assert_eq!(stats.states_found, checker.test_seen_fps_len());
                assert_eq!(stats.states_found, 2);
            }
            other => panic!("expected prefix storage fault, got {other:?}"),
        }

        assert_eq!(checker.test_seen_fps_len(), 2);
        assert_eq!(flat_queue.len(), 1);
        assert_eq!(flat_queue.flat_pushed(), 2);
    }

    #[test]
    fn compiled_bfs_fused_batch_admission_treats_duplicate_at_mmap_load_limit_as_already_present() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsBatchAdmissionMmapDuplicateLimitTest ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(DuplicateSuccessorFusedLevel));
        checker.compiled_bfs_step = None;
        let storage = FingerprintStorage::mmap(1, None)
            .expect("test mmap fingerprint storage should initialize");
        checker.set_fingerprint_storage(Arc::new(storage) as Arc<dyn FingerprintSet>);

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        let parent_fp = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        checker
            .mark_state_seen_fp_only_checked(parent_fp, None, 0)
            .expect("seed parent fingerprint");
        flat_queue.push_raw_buffer(&[0], parent_fp, 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 1);
                assert_eq!(stats.states_found, 1);
                assert_eq!(stats.max_depth, 1);
            }
            other => panic!("expected duplicate-at-load-limit success, got {other:?}"),
        }
        assert_eq!(checker.test_seen_fps_len(), 1);
        assert_eq!(flat_queue.len(), 0);
        assert_eq!(flat_queue.flat_pushed(), 1);
    }

    #[test]
    fn compiled_bfs_fused_success_rejects_short_parents_processed() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(ShortSuccessfulFusedLevel));
        checker.compiled_bfs_step = None;

        let (mut flat_queue, mut storage, _fp0, _fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("processed 1 parents for current level of 2"),
                    "short parents_processed should fail closed, got: {message}"
                );
            }
            other => panic!("expected short parents_processed error, got {other:?}"),
        }
        assert_eq!(flat_queue.len(), 2);
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn compiled_bfs_fused_deadlock_accepts_complete_level_metadata() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: true,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(CompleteDeadlockMetadataFusedLevel));
        checker.compiled_bfs_step = None;

        let (mut flat_queue, mut storage, _fp0, _fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Deadlock { trace, stats } => {
                assert_eq!(trace.len(), 1);
                assert_eq!(stats.transitions, 1);
            }
            other => panic!("expected complete-metadata fused deadlock, got {other:?}"),
        }
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn compiled_bfs_fused_zero_generated_without_raw_gap_is_not_deadlock() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: true,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(ZeroGeneratedDeadlockMetadataFusedLevel {
            first_zero_generated_parent_idx: tla_llvm2::LLVM2_BFS_NO_INDEX,
        }));
        checker.compiled_bfs_step = None;

        let (mut flat_queue, mut storage, _fp0, _fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 0);
            }
            other => panic!("expected zero-generated fused success without raw gap, got {other:?}"),
        }
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn compiled_bfs_fused_zero_generated_with_raw_gap_is_deadlock() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: true,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(ZeroGeneratedDeadlockMetadataFusedLevel {
            first_zero_generated_parent_idx: 0,
        }));
        checker.compiled_bfs_step = None;

        let (mut flat_queue, mut storage, _fp0, _fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Deadlock { trace, stats } => {
                assert_eq!(trace.len(), 1);
                assert_eq!(stats.transitions, 0);
            }
            other => panic!("expected zero-generated fused deadlock with raw gap, got {other:?}"),
        }
    }

    #[test]
    fn compiled_bfs_fused_invariant_failure_rejects_bad_parent_prefix() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(MalformedInvariantFusedLevel));
        checker.compiled_bfs_step = None;

        let (mut flat_queue, mut storage, _fp0, _fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("invariant metadata reported parent 1 with 1 parents"),
                    "bad invariant parent prefix should fail closed, got: {message}"
                );
            }
            other => panic!("expected malformed invariant metadata error, got {other:?}"),
        }
        assert_eq!(flat_queue.len(), 2);
    }

    #[test]
    fn compiled_bfs_fused_non_batch_admission_rejects_missing_parent_metadata() {
        let module = parse_module(
            r#"
	---- MODULE CompiledBfsBatchAdmissionMissingParentTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level =
            Some(Box::new(BatchAdmissionMissingParentMetadataFusedLevel {
                calls: AtomicUsize::new(0),
            }));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("without successor parent metadata"),
                    "missing parent metadata should fail closed, got: {message}"
                );
            }
            other => panic!("expected missing-parent-metadata error, got {other:?}"),
        }
        assert_eq!(checker.test_seen_fps_len(), 0);
        assert_eq!(flat_queue.len(), 0);
        assert_eq!(flat_queue.flat_pushed(), 1);
    }

    #[test]
    fn compiled_bfs_fused_non_batch_admission_rejects_parent_index_outside_current_level_after_append(
    ) {
        let module = parse_module(
            r#"
	---- MODULE CompiledBfsNonBatchOutOfRangeParentTest ----
	VARIABLE x
	Init == x = 0
	Next == x' = x + 1
	Inv == TRUE
	====
	"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(NonBatchOutOfRangeParentAfterAppendFusedLevel));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("parent index 1 for 1 parents"),
                    "out-of-range parent metadata should fail closed, got: {message}"
                );
            }
            other => panic!("expected out-of-range parent metadata error, got {other:?}"),
        }
        assert_eq!(checker.test_seen_fps_len(), 1);
        assert_eq!(flat_queue.len(), 1);
        assert_eq!(flat_queue.flat_pushed(), 2);
    }

    #[test]
    fn compiled_bfs_state_constrained_fused_buffer_overflow_returns_error_without_per_parent_fallback(
    ) {
        let module = parse_module(
            r#"
	---- MODULE CompiledBfsStateConstrainedOverflowTest ----
	VARIABLE x
	Init == x = 0
	Next == x' = x + 1
	Constraint == x <= 0
	====
	"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            check_deadlock: false,
            ..Default::default()
        };
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(BufferOverflowFusedLevel));
        checker.compiled_bfs_step = Some(Box::new(CountingCompiledStep {
            calls: step_calls.clone(),
        }));

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("state-constrained compiled BFS fused level failed closed"),
                    "state-constrained fused overflow should fail closed, got: {message}"
                );
            }
            other => panic!("expected state-constrained overflow error, got {other:?}"),
        }
        assert_eq!(
            step_calls.load(Ordering::SeqCst),
            0,
            "state-constrained fused overflow must not retry through per-parent compiled step"
        );
    }

    #[test]
    fn compiled_bfs_state_constrained_missing_raw_metadata_fails_closed_without_fallback() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsStateConstrainedMetadataTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Constraint == x <= 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            check_deadlock: true,
            ..Default::default()
        };
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level =
            Some(Box::new(BatchAdmissionMissingParentMetadataFusedLevel {
                calls: AtomicUsize::new(0),
            }));
        checker.compiled_bfs_step = Some(Box::new(CountingCompiledStep {
            calls: step_calls.clone(),
        }));

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("state-constrained compiled BFS fused level failed closed")
                        && message.contains("raw-successor metadata"),
                    "state-constrained metadata gap should fail closed, got: {message}"
                );
            }
            other => panic!("expected state-constrained metadata error, got {other:?}"),
        }
        assert_eq!(
            step_calls.load(Ordering::SeqCst),
            0,
            "state-constrained metadata gap must not retry through per-parent compiled step"
        );
    }

    #[test]
    fn compiled_bfs_per_parent_step_records_successor_parent_trace_loc() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.set_trace_file(TraceFile::create_temp().expect("trace file should initialize"));
        checker.compiled_bfs_level = None;
        checker.compiled_bfs_step = Some(Box::new(TraceProvenanceCompiledStep));

        checker.trace.cached_next_name = Some("Next".to_string());
        checker.trace.cached_resolved_next_name = Some("Next".to_string());
        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));

        let fp0 = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[0]);
        checker
            .mark_state_seen_fp_only_checked(fp0, None, 0)
            .expect("seed x=0");
        let loc0 = checker.trace.last_inserted_trace_loc;
        let fp1 = crate::check::model_checker::invariants::fingerprint_flat_compiled(&[1]);
        checker
            .mark_state_seen_fp_only_checked(fp1, None, 0)
            .expect("seed x=1");
        let loc1 = checker.trace.last_inserted_trace_loc;

        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], fp0, 0, loc0);
        flat_queue.push_raw_buffer(&[1], fp1, 0, loc1);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            checker.ctx.var_registry().len(),
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        assert!(matches!(result, CheckResult::Success(_)), "got {result:?}");
        let successor_10_fp =
            crate::check::model_checker::invariants::fingerprint_flat_compiled(&[10]);
        let successor_20_fp =
            crate::check::model_checker::invariants::fingerprint_flat_compiled(&[20]);
        let parents = checker
            .trace
            .trace_file
            .as_mut()
            .expect("trace file still installed")
            .build_parents_map()
            .expect("parents map should scan");
        assert_eq!(parents.get(&successor_10_fp), Some(&fp0));
        assert_eq!(parents.get(&successor_20_fp), Some(&fp1));
    }

    #[test]
    fn compiled_bfs_liveness_falls_back_when_fused_parent_metadata_missing() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsLivenessMissingParentTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.liveness_cache.cache_for_liveness = true;
        checker.compiled_bfs_level =
            Some(Box::new(BatchAdmissionMissingParentMetadataFusedLevel {
                calls: AtomicUsize::new(0),
            }));
        checker.compiled_bfs_step = Some(Box::new(CountingCompiledStep {
            calls: step_calls.clone(),
        }));

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 1);
                assert_eq!(stats.max_depth, 1);
                assert_eq!(stats.states_found, 1);
            }
            other => panic!("expected liveness fallback success, got {other:?}"),
        }
        assert!(step_calls.load(Ordering::SeqCst) > 0);
        assert_eq!(checker.test_seen_fps_len(), 1);
    }

    #[test]
    fn compiled_bfs_liveness_falls_back_when_fused_state_graph_edges_incomplete() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let fused_calls = Arc::new(AtomicUsize::new(0));
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.liveness_cache.cache_for_liveness = true;
        checker.compiled_bfs_level = Some(Box::new(UnsafeLocalDedupFusedLevel {
            calls: fused_calls.clone(),
        }));
        checker.compiled_bfs_step = Some(Box::new(CompleteTwoParentCompiledStep {
            calls: step_calls.clone(),
        }));

        let (mut flat_queue, mut storage, fp0, fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        assert!(matches!(result, CheckResult::Success(_)), "got {result:?}");
        assert_eq!(fused_calls.load(Ordering::SeqCst), 1);
        assert!(step_calls.load(Ordering::SeqCst) > 0);
        assert!(checker.compiled_bfs_level.is_none());
        assert_both_parent_liveness_edges(&checker, fp0, fp1);
    }

    #[test]
    fn compiled_bfs_state_constrained_liveness_metadata_gap_fails_closed() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsStateConstrainedLivenessMetadataTest ----
VARIABLE x
Init == x = 0 \/ x = 1
Next == \/ /\ x = 0 /\ x' = 2
        \/ /\ x = 1 /\ x' = 2
Constraint == x <= 1
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            check_deadlock: false,
            ..Default::default()
        };
        let fused_calls = Arc::new(AtomicUsize::new(0));
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.liveness_cache.cache_for_liveness = true;
        checker.compiled_bfs_level = Some(Box::new(UnsafeLocalDedupFusedLevel {
            calls: fused_calls.clone(),
        }));
        checker.compiled_bfs_step = Some(Box::new(CompleteTwoParentCompiledStep {
            calls: step_calls.clone(),
        }));

        let (mut flat_queue, mut storage, _fp0, _fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("state-constrained compiled BFS fused level failed closed")
                        && message.contains("state-graph successor")
                        && message.contains("liveness capture"),
                    "state-constrained liveness metadata gap should fail closed, got: {message}"
                );
            }
            other => panic!("expected state-constrained liveness metadata error, got {other:?}"),
        }
        assert_eq!(fused_calls.load(Ordering::SeqCst), 1);
        assert_eq!(
            step_calls.load(Ordering::SeqCst),
            0,
            "state-constrained liveness metadata gap must not retry through per-parent compiled step"
        );
        assert!(
            checker.compiled_bfs_level.is_some(),
            "fail-closed liveness metadata error must not clear the fused level for fallback"
        );
    }

    #[test]
    fn compiled_bfs_liveness_falls_back_when_per_parent_step_dedups_edges() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.liveness_cache.cache_for_liveness = true;
        checker.compiled_bfs_level = None;
        checker.compiled_bfs_step = Some(Box::new(UnsafeDedupingCompiledStep {
            calls: step_calls.clone(),
        }));

        let (mut flat_queue, mut storage, fp0, fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        assert!(matches!(result, CheckResult::Success(_)), "got {result:?}");
        assert_eq!(step_calls.load(Ordering::SeqCst), 0);
        assert_both_parent_liveness_edges(&checker, fp0, fp1);
    }

    #[test]
    fn compiled_bfs_liveness_clears_unsafe_step_when_prerequisite_falls_back() {
        let module = two_parent_liveness_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let step_calls = Arc::new(AtomicUsize::new(0));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = false;
        checker.liveness_cache.cache_for_liveness = true;
        checker.compiled_bfs_level = None;
        checker.compiled_bfs_step = Some(Box::new(UnsafeDedupingCompiledStep {
            calls: step_calls.clone(),
        }));

        let (mut flat_queue, mut storage, fp0, fp1) = seed_two_parent_flat_frontier(&mut checker);

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        assert!(matches!(result, CheckResult::Success(_)), "got {result:?}");
        assert_eq!(step_calls.load(Ordering::SeqCst), 0);
        assert!(checker.compiled_bfs_step.is_none());
        assert!(checker.compiled_bfs_level.is_none());
        assert_both_parent_liveness_edges(&checker, fp0, fp1);
    }

    #[test]
    fn fused_successor_pre_seen_lookup_needed_for_rust_invariant_filtering() {
        assert!(fused_successor_needs_pre_seen_lookup(false, 2));
    }

    #[test]
    fn fused_successor_pre_seen_lookup_skipped_after_backend_invariant_checking() {
        assert!(!fused_successor_needs_pre_seen_lookup(true, 2));
    }

    #[test]
    fn fused_successor_pre_seen_lookup_skipped_when_no_regular_invariants_exist() {
        assert!(!fused_successor_needs_pre_seen_lookup(false, 0));
    }

    #[test]
    fn fused_successor_rust_regular_invariant_check_skipped_when_none_configured() {
        assert!(!fused_successor_needs_rust_regular_invariant_check(
            false, 0,
        ));
    }

    #[test]
    fn fused_successor_rust_regular_invariant_check_skipped_when_backend_checked() {
        assert!(!fused_successor_needs_rust_regular_invariant_check(true, 2));
    }

    #[test]
    fn fused_successor_rust_regular_invariant_check_needed_for_action_only_backend() {
        assert!(fused_successor_needs_rust_regular_invariant_check(false, 2,));
    }

    #[test]
    fn compiled_bfs_fused_duplicate_only_level_counts_transitions_and_depth() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsDuplicateOnlyStatsTest ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            check_deadlock: false,
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(DuplicateOnlyFusedLevel));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        checker.flat_bfs_adapter = Some(crate::state::FlatBfsAdapter::from_layout(layout.clone()));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.transitions, 1);
                assert_eq!(stats.max_depth, 1);
            }
            other => panic!("expected duplicate-only fused level success, got {other:?}"),
        }
    }

    #[test]
    fn compiled_bfs_loop_returns_fatal_error_without_fallback() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsFatalRuntimeErrorTest ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(FatalFusedLevel));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("compiled BFS fatal error"),
                    "fatal compiled BFS error should be returned directly, got: {message}"
                );
            }
            other => panic!("expected fatal compiled BFS error, got {other:?}"),
        }
        assert!(
            checker.compiled_bfs_level.is_some(),
            "fatal fused-level errors must not clear the level and fall back"
        );
        assert!(
            !checker.jit_monolithic_disabled,
            "fatal fused-level errors must not disable compiled BFS and retry through fallback"
        );
    }

    #[test]
    fn compiled_bfs_loop_returns_preflight_fatal_error_without_fallback_or_level_call() {
        let module = parse_module(
            r#"
---- MODULE CompiledBfsPreflightFatalRuntimeErrorTest ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let preflight_seen = Arc::new(AtomicBool::new(false));
        let run_called = Arc::new(AtomicBool::new(false));
        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;
        checker.compiled_bfs_level = Some(Box::new(PreflightFatalFusedLevel {
            preflight_seen: preflight_seen.clone(),
            run_called: run_called.clone(),
        }));
        checker.compiled_bfs_step = None;

        let layout = Arc::new(StateLayout::new(
            checker.ctx.var_registry(),
            vec![VarLayoutKind::Scalar],
        ));
        let mut flat_queue = FlatBfsFrontier::new(layout);
        flat_queue.push_raw_buffer(&[0], Fingerprint(1), 0, 0);
        let mut storage = FingerprintOnlyStorage::new(
            BulkStateStorage::empty(checker.ctx.var_registry().len()),
            1,
        );

        let result = checker.run_compiled_bfs_loop(&mut storage, &mut flat_queue);

        assert!(
            preflight_seen.load(Ordering::SeqCst),
            "fused level preflight should run before the native level call"
        );
        assert!(
            !run_called.load(Ordering::SeqCst),
            "fatal preflight must stop before run_level_fused_arena"
        );
        match result {
            CheckResult::Error { error, .. } => {
                let message = error.to_string();
                assert!(
                    message.contains("compiled BFS fatal error"),
                    "fatal compiled BFS preflight error should be returned directly, got: {message}"
                );
            }
            other => panic!("expected fatal compiled BFS preflight error, got {other:?}"),
        }
        assert!(
            checker.compiled_bfs_level.is_some(),
            "fatal fused-level preflight errors must not clear the level and fall back"
        );
        assert!(
            !checker.jit_monolithic_disabled,
            "fatal fused-level preflight errors must not disable compiled BFS"
        );
    }
}
