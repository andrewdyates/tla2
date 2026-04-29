// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequential BFS transport implementation.
//!
//! Part of #2356 Phase 4 Step 4b: wraps `ModelChecker` + `BfsStorage` +
//! `BfsFrontier` behind the `BfsTransport` trait. All method calls are direct
//! (no synchronization) — the compiler monomorphizes through the trait to
//! produce identical code to the original `run_bfs_loop_core`.
//!
//! ## State Lifecycle
//!
//! Sequential mode uses `BfsStorage::return_current` to return the current
//! state to storage (needed by `FullStateStorage` to free the HashMap slot).
//! This is managed via `release_state()` on early exit paths and internally
//! by `process_successors()` (which wraps the state in a `BfsIterState` guard).

use super::super::frontier::BfsFrontier;
use super::super::run_helpers::BfsProfile;
use super::super::{ArrayState, CheckError, Fingerprint, Instant, ModelChecker};
use super::iter_state::BfsIterState;
use super::storage_modes::BfsStorage;
use super::successor_processing::BfsIterOutcome;
use super::transport::{BfsTermination, BfsTransport};
use super::BfsStepParams;
use crate::var_index::VarRegistry;
use tla_eval::eval_arena::ArenaStateGuard;

/// Sequential transport: single-threaded BFS with `VecDeque` queue.
///
/// Wraps `ModelChecker` + `BfsStorage` + `BfsFrontier` behind `BfsTransport`.
/// Zero synchronization overhead — all calls are direct field access and
/// method dispatch, identical to the original `run_bfs_loop_core` after
/// monomorphization.
///
/// Part of #2356 Phase 4 Step 4b.
pub(in crate::check::model_checker) struct SequentialTransport<
    'a,
    'mc,
    S: BfsStorage,
    Q: BfsFrontier<Entry = S::QueueEntry>,
> {
    pub(super) checker: &'mc mut ModelChecker<'a>,
    pub(super) storage: &'mc mut S,
    pub(super) queue: &'mc mut Q,
    pub(super) registry: VarRegistry,
    pub(super) prof: BfsProfile,
    pub(super) states_since_progress: usize,
    pub(super) start_time: Instant,
    pub(super) depth_limit_reached: bool,
    /// Part of #2751: memory pressure requested a checkpoint save.
    /// Set by `report_progress`, consumed by `should_checkpoint`.
    memory_checkpoint_due: bool,
    /// Part of #2751: memory pressure requested exploration stop.
    /// Set by `report_progress`, consumed by `check_state_limit`.
    memory_stop_requested: bool,
    /// Part of #3282: which limit type triggered a deferred stop.
    stop_limit_type: Option<super::super::LimitType>,
    /// Part of #3768: frontier sampler for CDEMC cooperative state.
    /// Active only when the ModelChecker has a cooperative state configured.
    #[cfg(feature = "z4")]
    frontier_sampler: Option<super::frontier_sampler::FrontierSampler>,
}

impl<'a, 'mc, S: BfsStorage, Q: BfsFrontier<Entry = S::QueueEntry>>
    SequentialTransport<'a, 'mc, S, Q>
{
    /// Create a new sequential transport.
    ///
    /// The `registry` is cloned from `checker.ctx.var_registry()` at construction
    /// to avoid repeated clones during the loop.
    pub(in crate::check::model_checker) fn new(
        checker: &'mc mut ModelChecker<'a>,
        storage: &'mc mut S,
        queue: &'mc mut Q,
    ) -> Self {
        let registry = checker.ctx.var_registry().clone();
        let start_time = Instant::now();
        checker.reset_jit_profile_counters();
        let prof = BfsProfile::new(start_time);
        // Part of #3768: create frontier sampler if cooperative state is configured.
        #[cfg(feature = "z4")]
        let frontier_sampler = checker.cooperative.as_ref().map(|coop| {
            super::frontier_sampler::FrontierSampler::new(coop.clone(), registry.clone())
        });
        Self {
            checker,
            storage,
            queue,
            registry,
            prof,
            states_since_progress: 0,
            start_time,
            depth_limit_reached: false,
            memory_checkpoint_due: false,
            memory_stop_requested: false,
            stop_limit_type: None,
            #[cfg(feature = "z4")]
            frontier_sampler,
        }
    }
}

impl<'a, 'mc, S: BfsStorage, Q: BfsFrontier<Entry = S::QueueEntry>> BfsTransport
    for SequentialTransport<'a, 'mc, S, Q>
{
    type WorkItem = S::QueueEntry;

    fn try_dequeue(&mut self) -> Option<Self::WorkItem> {
        self.queue.pop()
    }

    fn resolve(
        &mut self,
        item: Self::WorkItem,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, BfsTermination> {
        match self.storage.dequeue(item, self.checker) {
            Ok(result) => Ok(result),
            Err(result) => {
                // Part of #2774: flush coverage totals before returning dequeue error.
                self.checker.update_coverage_totals();
                Err(BfsTermination::result(result))
            }
        }
    }

    fn report_progress(
        &mut self,
        depth: usize,
        queue_len: usize,
    ) -> Result<(), super::transport::BfsTermination> {
        use super::super::run::ProgressAction;

        let action = self.checker.maybe_report_progress(
            &mut self.states_since_progress,
            &self.start_time,
            depth,
            queue_len,
        );
        match action {
            ProgressAction::Continue => Ok(()),
            ProgressAction::Checkpoint => {
                // Part of #2751 Phase 2: memory-triggered checkpoint on Warning.
                // Set flag so should_checkpoint() fires on the next call,
                // which has access to `current` for a complete checkpoint.
                self.memory_checkpoint_due = true;
                Ok(())
            }
            ProgressAction::StopWithCheckpoint(limit_type) => {
                // Part of #2751 Phase 3 / #3282: save checkpoint then stop.
                // Set both flags: should_checkpoint() saves with current,
                // then check_state_limit() stops exploration.
                self.memory_checkpoint_due = true;
                self.memory_stop_requested = true;
                self.stop_limit_type = Some(limit_type);
                Ok(())
            }
            ProgressAction::Stop(limit_type) => Err(super::transport::BfsTermination::result(
                super::super::CheckResult::LimitReached {
                    limit_type,
                    stats: self.checker.stats.clone(),
                },
            )),
        }
    }

    fn should_checkpoint(&self) -> bool {
        self.memory_checkpoint_due || self.checker.should_save_checkpoint()
    }

    fn save_checkpoint(&mut self, current: &ArrayState) {
        self.memory_checkpoint_due = false;
        let frontier =
            self.storage
                .checkpoint_frontier(current, &*self.queue, &self.registry, self.checker);
        self.checker.save_checkpoint_now(&frontier);
    }

    fn check_state_limit(&mut self) -> Result<(), BfsTermination> {
        // Part of #2751 Phase 3 / #3282: stop after resource-triggered checkpoint.
        if self.memory_stop_requested {
            self.memory_stop_requested = false;
            let limit_type = self
                .stop_limit_type
                .take()
                .unwrap_or(super::super::LimitType::Memory);
            return Err(BfsTermination::result(
                super::super::CheckResult::LimitReached {
                    limit_type,
                    stats: self.checker.stats.clone(),
                },
            ));
        }
        if let Some(result) = self.checker.check_state_limit() {
            Err(BfsTermination::result(
                self.checker.finalize_terminal_result_with_storage(result),
            ))
        } else {
            Ok(())
        }
    }

    fn release_state(&mut self, fp: Fingerprint, current: ArrayState) {
        self.storage.return_current(fp, current, self.checker);
    }

    fn on_depth_limit_skip(&mut self) {
        self.depth_limit_reached = true;
    }

    fn process_successors(
        &mut self,
        fp: Fingerprint,
        current: ArrayState,
        depth: usize,
        succ_depth: usize,
        current_level: u32,
        succ_level: u32,
    ) -> Result<(), BfsTermination> {
        // Part of #3580: keep the arena lifecycle panic-safe across successor eval.
        let _arena_state = ArenaStateGuard::new();

        // Part of #3989: profile state variable types for Tier 2 specialization.
        // Runs during warmup only (~1000 states); after freeze, this is a no-op.
        self.checker.profile_state_types(&current);

        // Set the TLC level on the eval context for this iteration.
        self.checker.ctx.set_tlc_level(current_level);

        // Part of #3083: update TLCGet("stats") runtime stats from BFS state.
        // Without this, BFS mode always falls through to hardcoded zeros in
        // builtin_tlc_get.rs. The plumbing via set_tlc_runtime_stats already
        // exists (used by simulation mode) — BFS just never called it.
        self.checker
            .ctx
            .set_tlc_runtime_stats(Some(crate::eval::TlcRuntimeStats::new(
                self.checker.stats.states_generated() as i64,
                self.checker.stats.states_found as i64,
                self.queue.len() as i64,
                0, // traces: not applicable in BFS mode
                i64::from(current_level),
            )));

        // Part of #3785: oracle-based action routing for fused cooperative mode.
        // When the oracle routes ALL actions to SymbolicOnly, BFS skips
        // successor generation entirely for this state — the symbolic engine
        // (BMC/PDR) handles all actions. This is zero-overhead when cooperative
        // mode is inactive: the check short-circuits on `self.cooperative.is_none()`.
        if self.checker.cooperative_oracle_skips_all_actions() {
            // State was explored (dequeued) but no successors generated by BFS.
            // The symbolic engine is responsible for expanding this state.
            // Return the state to storage without generating successors.
            self.storage.return_current(fp, current, self.checker);
            return Ok(());
        }

        // Create the BfsIterState guard (ensures return_to is called).
        let mut iter_state = BfsIterState::new(fp, current);

        // Bundle value parameters for successor processing.
        let params = BfsStepParams {
            registry: &self.registry,
            current_depth: depth,
            succ_depth,
            current_level,
            succ_level,
        };

        // Dispatch to diff or full-state successor processing.
        let outcome = if self.storage.use_diffs(self.checker) {
            if let Some(outcome) = self.checker.process_diff_successors(
                &mut iter_state,
                self.storage,
                self.queue,
                &params,
                &mut self.prof,
            ) {
                outcome
            } else {
                // Diff generation returned None; fall through to full-state.
                self.checker.process_full_state_successors(
                    &mut iter_state,
                    self.storage,
                    self.queue,
                    &params,
                    &mut self.prof,
                )
            }
        } else {
            self.checker.process_full_state_successors(
                &mut iter_state,
                self.storage,
                self.queue,
                &params,
                &mut self.prof,
            )
        };

        match outcome {
            BfsIterOutcome::Continue => Ok(()),
            BfsIterOutcome::Terminate(result) => Err(BfsTermination::result(
                self.checker.with_current_storage_stats(result),
            )),
        }
    }

    fn handle_error(
        &mut self,
        fp: Fingerprint,
        current: ArrayState,
        error: CheckError,
    ) -> BfsTermination {
        // Create a temporary BfsIterState guard for the error return path.
        let mut iter_state = BfsIterState::new(fp, current);
        let result = self
            .checker
            .bfs_error_return(&mut iter_state, self.storage, error);
        BfsTermination::result(self.checker.with_current_storage_stats(result))
    }

    fn output_profile(&self) {
        // Part of #3990: snapshot arena stats into profile before output.
        // We collect arena stats inline since output_profile is called on the
        // worker thread where the thread-local arena is accessible.
        let mut prof_with_arena = self.prof.clone();
        prof_with_arena.snapshot_arena_stats();
        ModelChecker::output_bfs_profile(&prof_with_arena);
        // Part of #3580: report arena allocation stats when TLA2_ARENA_STATS=1.
        tla_eval::eval_arena::report_arena_stats();
        // Part of #3990: report per-worker state arena stats.
        crate::arena::report_worker_arena_stats();
    }

    fn depth_limit_reached(&self) -> bool {
        self.depth_limit_reached
    }

    fn maybe_periodic_liveness(&mut self) -> Result<(), BfsTermination> {
        if let Some(result) = self.checker.maybe_periodic_liveness(&self.start_time) {
            return Err(BfsTermination::result(
                self.checker.finalize_terminal_result_with_storage(result),
            ));
        }
        Ok(())
    }

    /// Part of #3768: sample frontier states for CDEMC cooperative engines.
    /// Part of #3871: also pass total_states so FrontierSampler can call
    /// record_convergence at level boundaries.
    fn maybe_sample_frontier(&mut self, _depth: usize, _state: &super::super::ArrayState) {
        #[cfg(feature = "z4")]
        if let Some(ref mut sampler) = self.frontier_sampler {
            let total_states = self.checker.stats.states_found as u64;
            sampler.on_state(_depth, _state, total_states);
        }
    }
}
