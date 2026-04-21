// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BFS exploration engine: entry points for sequential model checking.
//!
//! Part of #2351: extracted from `run_bfs_common.rs`.
//! Part of #2356 Phase 4 Step 4d: the BFS loop body is now in `worker_loop.rs`
//! (`run_bfs_worker`). This module provides the entry points that construct
//! `SequentialTransport` and delegate to the unified loop.

use super::super::frontier::BfsFrontier;
use super::super::{CheckResult, ModelChecker};
use super::storage_modes::BfsStorage;
use super::transport::BfsWorkerConfig;
use super::transport_seq::SequentialTransport;
use super::worker_loop::{run_bfs_worker, BfsLoopOutcome};
use crate::shared_verdict::Verdict;
use crate::arena::init_worker_arena;
use tla_eval::eval_arena::init_thread_arena;

impl ModelChecker<'_> {
    /// Unified BFS exploration loop, generic over storage mode.
    ///
    /// Calls `run_bfs_loop_core` for the BFS iteration, then
    /// `finish_check_after_bfs` for post-loop finalization (liveness,
    /// postcondition, storage error checks).
    ///
    /// Part of #2133.
    pub(in crate::check::model_checker) fn run_bfs_loop<S: BfsStorage>(
        &mut self,
        storage: &mut S,
        queue: &mut impl BfsFrontier<Entry = S::QueueEntry>,
    ) -> CheckResult {
        let result = match self.run_bfs_loop_core(storage, queue) {
            BfsLoopOutcome::Terminated(result) => *result,
            BfsLoopOutcome::Complete {
                depth_limit_reached,
            } => self.finish_check_after_bfs(depth_limit_reached, false),
        };
        // Part of #3717: publish BFS verdict to portfolio SharedVerdict.
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
        // Part of #3767: publish BFS verdict to cooperative SharedVerdict.
        // This enables the symbolic lane (BMC/PDR) to observe BFS completion
        // and exit early in fused CDEMC mode.
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
            // Part of #4002: signal BFS completion so cooperative BMC loop
            // exits cleanly even when verdict is Unknown.
            coop.mark_bfs_complete();
        }
        result
    }

    /// Core BFS iteration loop, generic over storage mode.
    ///
    /// Constructs a [`SequentialTransport`] and delegates to the unified
    /// [`run_bfs_worker`] loop body. Returns `BfsLoopOutcome` so callers
    /// can select `resume_mode` when calling `finish_check_after_bfs`.
    ///
    /// Part of #2356 Phase 4 Step 4d: replaces the previous ~140-line inline
    /// loop with a single call to the unified BFS worker loop.
    pub(in crate::check::model_checker) fn run_bfs_loop_core<S: BfsStorage>(
        &mut self,
        storage: &mut S,
        queue: &mut impl BfsFrontier<Entry = S::QueueEntry>,
    ) -> BfsLoopOutcome {
        // Part of #3580: Initialize eval arena on the main thread for sequential BFS.
        init_thread_arena();

        // Part of #3990: Initialize worker arena for successor state allocation.
        init_worker_arena();

        let config = BfsWorkerConfig {
            max_depth: self.exploration.max_depth,
        };
        // Part of #3717: clone the Arc to avoid holding an immutable borrow on
        // `self` across the mutable borrow needed by SequentialTransport.
        let portfolio_verdict = self.portfolio_verdict.clone();
        // Part of #3767: clone the cooperative Arc so we can reference its
        // verdict field after `self` is mutably borrowed by SequentialTransport.
        #[cfg(feature = "z4")]
        let cooperative = self.cooperative.clone();
        let mut transport = SequentialTransport::new(self, storage, queue);
        // Part of #3767: use cooperative verdict for early-exit if in fused mode,
        // falling back to the standalone portfolio verdict.
        #[cfg(feature = "z4")]
        let verdict_ref = cooperative
            .as_ref()
            .map(|c| c.verdict.as_ref())
            .or(portfolio_verdict.as_deref());
        #[cfg(not(feature = "z4"))]
        let verdict_ref = portfolio_verdict.as_deref();
        run_bfs_worker(&mut transport, &config, verdict_ref)
    }
}
