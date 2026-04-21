// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
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

#[cfg(feature = "jit")]
use super::flat_frontier::FlatBfsFrontier;
#[cfg(feature = "jit")]
use super::storage_modes::FingerprintOnlyStorage;
#[cfg(feature = "jit")]
use super::super::{CheckResult, ModelChecker, Trace};
#[cfg(feature = "jit")]
use crate::check::model_checker::frontier::BfsFrontier;
#[cfg(feature = "jit")]
use crate::shared_verdict::Verdict;
#[cfg(feature = "jit")]
use crate::state::FlatState;

/// Statistics from a compiled BFS level loop run.
#[cfg(feature = "jit")]
#[derive(Debug, Default)]
pub(in crate::check::model_checker) struct CompiledBfsLoopStats {
    /// Total parents processed across all levels.
    pub(in crate::check::model_checker) parents_processed: u64,
    /// Total successors generated (before global dedup).
    pub(in crate::check::model_checker) successors_generated: u64,
    /// Total new successors after global dedup.
    pub(in crate::check::model_checker) successors_new: u64,
    /// BFS levels completed.
    pub(in crate::check::model_checker) levels_completed: usize,
}

#[cfg(feature = "jit")]
impl ModelChecker<'_> {
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
            return self.run_bfs_loop(storage, flat_queue);
        }

        let registry = self.ctx.var_registry().clone();
        let mut stats = CompiledBfsLoopStats::default();
        let mut depth_limit_reached = false;

        // Initialize eval arena for sequential BFS.
        tla_eval::eval_arena::init_thread_arena();
        crate::arena::init_worker_arena();

        let use_fused = self.fused_bfs_level_available();
        eprintln!(
            "[compiled-bfs] starting compiled BFS level loop ({} initial states in arena, fused={})",
            flat_queue.len(),
            use_fused,
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

            // Get the remaining flat frontier arena.
            let arena_data = flat_queue.remaining_arena();
            let (arena, parent_count) = match arena_data {
                Some((a, c)) if c > 0 => (a.to_vec(), c),
                _ => break, // Frontier empty -- BFS complete
            };

            // We need to read the compiled step's state_len before borrowing
            // mutable self in the loop below.
            let state_len = match self.compiled_bfs_step.as_ref() {
                Some(s) => s.state_len(),
                None => {
                    eprintln!(
                        "[compiled-bfs] compiled step became unavailable, \
                         falling back to standard BFS loop"
                    );
                    return self.run_bfs_loop(storage, flat_queue);
                }
            };

            // Determine successor depth from the first parent's metadata.
            // All parents in this level share the same depth (BFS invariant).
            let (_first_fp, first_depth, _first_trace_loc) =
                match flat_queue.meta_at_offset(0) {
                    Some(m) => m,
                    None => break,
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

            // Part of #4171: Fused BFS level path — process entire frontier
            // in a single native function call when the fused level is available.
            // Falls back to the per-parent step loop on error.
            if use_fused {
                if let Some(ref level) = self.compiled_bfs_level {
                    match level.run_level_fused_arena(&arena, parent_count) {
                        Some(Ok(level_result)) => {
                            // Handle invariant violation from fused level.
                            if !level_result.invariant_ok {
                                if let Some(inv_idx) = level_result.failed_invariant_idx {
                                    let inv_name = self
                                        .config
                                        .invariants
                                        .get(inv_idx as usize)
                                        .cloned()
                                        .unwrap_or_else(|| format!("invariant_{inv_idx}"));

                                    let state = level_result
                                        .failed_parent_idx
                                        .and_then(|pidx| {
                                            let start = pidx * state_len;
                                            let end = start + state_len;
                                            arena.get(start..end)
                                        })
                                        .map(|buf| {
                                            self.reconstruct_state_from_flat(buf, &registry)
                                        })
                                        .unwrap_or_else(|| {
                                            self.reconstruct_state_from_flat(
                                                &arena[..state_len],
                                                &registry,
                                            )
                                        });

                                    flat_queue.advance_read_cursor(parent_count);
                                    stats.parents_processed +=
                                        level_result.parents_processed as u64;
                                    stats.successors_generated += level_result.total_generated;
                                    stats.successors_new += level_result.total_new;
                                    self.report_compiled_bfs_stats(&stats);

                                    return CheckResult::InvariantViolation {
                                        invariant: inv_name,
                                        trace: Trace::from_states(vec![state]),
                                        stats: self.stats.clone(),
                                    };
                                }
                            }

                            // Process the fused level's successors through global dedup.
                            // Clone the bridge to avoid holding an immutable borrow on
                            // `self.flat_bfs_adapter` while calling mutable methods below.
                            let bridge = self
                                .flat_bfs_adapter
                                .as_ref()
                                .expect(
                                    "invariant: flat_bfs_adapter present in compiled BFS",
                                )
                                .bridge()
                                .clone();

                            let mut global_new: u64 = 0;
                            for succ_buf in &level_result.new_successors {
                                let succ_fp = bridge
                                    .traditional_fingerprint_from_buffer(succ_buf, &registry);

                                // Global dedup check.
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

                                match self.mark_state_seen_fp_only_checked(
                                    succ_fp,
                                    None,
                                    succ_depth,
                                ) {
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
                                flat_queue.push_raw_buffer(
                                    succ_buf,
                                    succ_fp,
                                    succ_depth,
                                    trace_loc,
                                );
                            }

                            flat_queue.advance_read_cursor(parent_count);
                            stats.parents_processed +=
                                level_result.parents_processed as u64;
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
                            self.stats.states_found = self.states_count();
                            let total_states = self.states_count();
                            if stats.levels_completed % 5 == 0 || total_states > 100_000 {
                                eprintln!(
                                    "[compiled-bfs] fused level {}: {} states, {} generated, {} new, queue={}",
                                    stats.levels_completed,
                                    total_states,
                                    stats.successors_generated,
                                    stats.successors_new,
                                    flat_queue.len(),
                                );
                            }

                            crate::arena::worker_arena_reset();

                            if depth_limit_reached {
                                break;
                            }
                            continue;
                        }
                        Some(Err(e)) => {
                            eprintln!(
                                "[compiled-bfs] fused level error: {e} — \
                                 falling back to per-parent step"
                            );
                            // Fall through to per-parent loop below.
                        }
                        None => {
                            // Fused function not available (shouldn't happen
                            // since use_fused checked has_fused_level).
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

            for parent_idx in 0..parent_count {
                let start = parent_idx * state_len;
                let end = start + state_len;
                let parent_slice = &arena[start..end];

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
                let step = self.compiled_bfs_step.as_ref().expect(
                    "invariant: compiled_bfs_step present in compiled BFS loop",
                );
                let output = match step.step_flat(parent_slice) {
                    Ok(output) => output,
                    Err(e) => {
                        eprintln!(
                            "[compiled-bfs] step error at depth {first_depth}, \
                             parent {parent_idx}: {e} -- disabling"
                        );
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

                level_parents += 1;
                level_generated += u64::from(output.generated_count);

                let had_raw_successors = output.generated_count > 0;

                // Handle invariant violation from compiled step.
                if !output.invariant_ok {
                    if let Some(inv_idx) = output.failed_invariant_idx {
                        let inv_name = self
                            .config
                            .invariants
                            .get(inv_idx as usize)
                            .cloned()
                            .unwrap_or_else(|| format!("invariant_{inv_idx}"));

                        // Reconstruct the failing successor for error reporting.
                        // Use the FlatBfsAdapter to convert from flat to array to State.
                        let failed_state = if let Some(failed_succ_idx) =
                            output.failed_successor_idx
                        {
                            output
                                .iter_successors()
                                .nth(failed_succ_idx as usize)
                                .map(|succ_slice| {
                                    self.reconstruct_state_from_flat(succ_slice, &registry)
                                })
                        } else {
                            None
                        };

                        let state = failed_state.unwrap_or_else(|| {
                            // Fallback: report the parent state.
                            self.reconstruct_state_from_flat(parent_slice, &registry)
                        });

                        flat_queue.advance_read_cursor(parent_idx + 1);
                        stats.parents_processed += level_parents;
                        stats.successors_generated += level_generated;
                        stats.successors_new += level_new;
                        self.report_compiled_bfs_stats(&stats);

                        return CheckResult::InvariantViolation {
                            invariant: inv_name,
                            trace: Trace::from_states(vec![state]),
                            stats: self.stats.clone(),
                        };
                    }
                }

                // Process new successors: second-level dedup against global seen set.
                // Clone the bridge to avoid holding an immutable borrow on
                // `self.flat_bfs_adapter` while calling mutable methods below.
                // Part of #3986: Phase 3 zero-alloc compiled BFS.
                let bridge = self
                    .flat_bfs_adapter
                    .as_ref()
                    .expect("invariant: flat_bfs_adapter present in compiled BFS")
                    .bridge()
                    .clone();

                for flat_succ in output.iter_successors() {
                    // Zero-allocation fast path: compute fingerprint directly
                    // from the raw &[i64] buffer without constructing FlatState
                    // (avoids Box<[i64]> heap allocation per successor).
                    // Part of #3986: Phase 3 zero-alloc compiled BFS.
                    let succ_fp = bridge
                        .traditional_fingerprint_from_buffer(flat_succ, &registry);

                    // Global dedup check.
                    match self.is_state_seen_checked(succ_fp) {
                        Ok(true) => continue, // Already seen globally
                        Ok(false) => {}       // New state
                        Err(result) => {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            self.report_compiled_bfs_stats(&stats);
                            return result;
                        }
                    }

                    // Mark as seen in global set.
                    match self.mark_state_seen_fp_only_checked(succ_fp, None, succ_depth) {
                        Ok(true) => {} // Successfully inserted
                        Ok(false) => continue, // Race condition (shouldn't happen in sequential)
                        Err(result) => {
                            flat_queue.advance_read_cursor(parent_idx + 1);
                            stats.parents_processed += level_parents;
                            self.report_compiled_bfs_stats(&stats);
                            return result;
                        }
                    }

                    level_new += 1;

                    // Get trace_loc from the last inserted state.
                    let trace_loc = self.trace.last_inserted_trace_loc;

                    // Zero-allocation enqueue: push raw buffer directly into
                    // the arena without constructing FlatState.
                    // Part of #3986: Phase 3 zero-alloc compiled BFS.
                    flat_queue.push_raw_buffer(
                        flat_succ,
                        succ_fp,
                        succ_depth,
                        trace_loc,
                    );
                }

                // Deadlock detection: if no successors were generated.
                if self.exploration.check_deadlock && !had_raw_successors {
                    let state = self.reconstruct_state_from_flat(parent_slice, &registry);
                    flat_queue.advance_read_cursor(parent_idx + 1);
                    stats.parents_processed += level_parents;
                    stats.successors_generated += level_generated;
                    stats.successors_new += level_new;
                    self.report_compiled_bfs_stats(&stats);

                    return CheckResult::Deadlock {
                        trace: Trace::from_states(vec![state]),
                        stats: self.stats.clone(),
                    };
                }
            }

            // Advance past all parents we processed.
            flat_queue.advance_read_cursor(consumed_count);
            stats.parents_processed += level_parents;
            stats.successors_generated += level_generated;
            stats.successors_new += level_new;
            stats.levels_completed += 1;

            // Update model checker stats.
            self.stats.states_found = self.states_count();

            // Progress reporting.
            let total_states = self.states_count();
            if stats.levels_completed % 5 == 0 || total_states > 100_000 {
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
    #[cfg(feature = "jit")]
    #[must_use]
    fn compiled_bfs_level_eligible(&self) -> bool {
        // Force-disable via config or env var.
        if self.config.use_compiled_bfs == Some(false) {
            return false;
        }
        if crate::check::debug::compiled_bfs_disabled() {
            return false;
        }
        if self.compiled_bfs_step.is_none() {
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
        if self.por.independence.is_some() {
            return false;
        }
        if self.coverage.collect && !self.coverage.actions.is_empty() {
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
    #[cfg(feature = "jit")]
    #[must_use]
    fn fused_bfs_level_available(&self) -> bool {
        self.compiled_bfs_level
            .as_ref()
            .is_some_and(|level| level.has_fused_level())
    }

    /// Reconstruct a TLA+ `State` from a flat i64 buffer.
    ///
    /// Uses the `FlatBfsAdapter` to convert flat -> ArrayState -> State.
    /// This is the cold path used only for error reporting (invariant
    /// violations, deadlock).
    ///
    /// Part of #3988.
    #[cfg(feature = "jit")]
    fn reconstruct_state_from_flat(
        &self,
        flat_buf: &[i64],
        registry: &crate::var_index::VarRegistry,
    ) -> crate::State {
        if let Some(ref adapter) = self.flat_bfs_adapter {
            let layout = adapter.layout().clone();
            let buffer: Box<[i64]> = flat_buf.to_vec().into_boxed_slice();
            let flat = FlatState::from_buffer(buffer, layout);
            let arr = adapter.bridge().to_array_state(&flat, registry);
            arr.to_state(registry)
        } else {
            // Fallback: treat each i64 as SmallInt.
            let values: Vec<_> = flat_buf
                .iter()
                .map(|&v| crate::Value::SmallInt(v))
                .collect();
            let arr = crate::state::ArrayState::from_values(values);
            arr.to_state(registry)
        }
    }

    /// Report compiled BFS loop statistics.
    #[cfg(feature = "jit")]
    fn report_compiled_bfs_stats(&self, stats: &CompiledBfsLoopStats) {
        eprintln!(
            "[compiled-bfs] completed: {} levels, {} parents, {} generated, {} new, {} total states",
            stats.levels_completed,
            stats.parents_processed,
            stats.successors_generated,
            stats.successors_new,
            self.states_count(),
        );
    }
}
