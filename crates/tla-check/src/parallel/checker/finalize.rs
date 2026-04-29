// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel checker finalization and result synthesis phase.

mod collect;
mod report;
mod resolve;

use super::*;

impl ParallelChecker {
    pub(super) fn finalize_check(
        &self,
        runtime: CheckRuntime,
        detected_actions: Vec<String>,
        detected_action_ids: Vec<String>,
        ctx: &mut EvalCtx,
        promoted_properties: Vec<String>,
        state_property_violation_names: Vec<String>,
    ) -> CheckResult {
        let CheckRuntime {
            result_rx,
            handles,
            num_initial,
            start_time,
            jit_compiled_invariants: _,
        } = runtime;

        // Phase 1: Spawn progress reporting thread (and capacity-warning loop).
        let progress_handle = self.spawn_progress_reporter(start_time);

        // Phase 2: Collect worker results with precedence-correct reduction.
        let collected = self.collect_worker_results(
            result_rx,
            ctx,
            num_initial,
            &detected_actions,
            &detected_action_ids,
            &promoted_properties,
            start_time,
        );

        // Phase 3: Emit profiling, disabled-action, timing, and enum-profile reports.
        report::emit_finalize_reports(
            &collected.total_stats,
            self.num_workers,
            self.config.jit_verify,
        );

        // Phase 4: Join threads, build final stats, resolve terminal result.
        self.join_and_resolve_terminal(
            collected,
            handles,
            progress_handle,
            ctx,
            num_initial,
            detected_actions,
            detected_action_ids,
            promoted_properties,
            state_property_violation_names,
        )
    }
}
