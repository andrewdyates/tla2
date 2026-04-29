// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Periodic maintenance during parallel BFS: liveness checks and checkpoints.
//!
//! Extracted from `finalize.rs` to keep files under the 500-line limit.
//! Part of #3175: periodic liveness checking during parallel exploration.

use super::*;
use crate::checkpoint::Checkpoint;
use crate::memory::MemoryPressure;

pub(super) struct PeriodicMaintenanceOutcome {
    pub(super) periodic_result: Option<CheckResult>,
    pub(super) checkpoint: Option<Checkpoint>,
}

impl ParallelChecker {
    pub(super) fn periodic_liveness_enabled(&self) -> bool {
        self.successors.is_some()
            && !self.config.liveness_execution.uses_on_the_fly()
            && !crate::check::debug::skip_liveness()
    }

    pub(super) fn snapshot_runtime_stats(
        &self,
        num_initial: usize,
        detected_actions: &[String],
        detected_action_ids: &[String],
    ) -> CheckStats {
        CheckStats {
            states_found: self.states_count(),
            initial_states: num_initial,
            max_queue_depth: self.max_queue_depth.load(Ordering::SeqCst),
            transitions: self.total_transitions.load(Ordering::SeqCst),
            max_depth: self.max_depth.load(Ordering::SeqCst),
            detected_actions: detected_actions.to_vec(),
            detected_action_ids: detected_action_ids.to_vec(),
            coverage: None,
            phantom_dequeues: 0,
            // Do not consume the shared counter mid-run; finalization drains it once.
            suppressed_guard_errors: 0,
            trace_reconstructions: 0,
            fp_dedup_collisions: self.fp_dedup_collisions(),
            internal_fp_collisions: self.internal_fp_collisions(),
            storage_stats: FingerprintSet::stats(&*self.seen_fps),
            collision_check_mode: Default::default(),
            collision_check_stats: Default::default(),
            symmetry_reduction: Default::default(),
            por_reduction: Default::default(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn run_periodic_maintenance(
        &self,
        ctx: &mut EvalCtx,
        num_initial: usize,
        detected_actions: &[String],
        detected_action_ids: &[String],
        promoted_properties: &[String],
        bfs_start_time: Instant,
        periodic_liveness: &mut crate::periodic_liveness::PeriodicLivenessState,
        checkpoint_due: bool,
    ) -> PeriodicMaintenanceOutcome {
        let current_states = self.states_count();
        let now = Instant::now();
        let liveness_due = self.periodic_liveness_enabled()
            && periodic_liveness.should_run(now, bfs_start_time, current_states);

        // Part of #4080: compute memory breakdown once for reuse.
        let breakdown = self.memory_breakdown();

        // Part of #4080: periodic memory logging for post-mortem analysis.
        if crate::memory::periodic_memory_log_enabled() {
            crate::memory::emit_memory_log(current_states, 0, &breakdown);
        }

        // Part of #4080: hard internal memory cap.
        let internal_memory_stop = if let Some(internal_limit) = self.internal_memory_limit {
            if breakdown.total_bytes > internal_limit {
                let used_mb = breakdown.total_bytes / (1024 * 1024);
                let limit_mb = internal_limit / (1024 * 1024);
                eprintln!(
                    "Error: internal memory ({used_mb} MB) exceeded hard cap ({limit_mb} MB) \
                     — stopping exploration."
                );
                eprintln!("  Breakdown: {}", breakdown.format_diagnostic());
                true
            } else {
                false
            }
        } else {
            false
        };

        // Part of #2751 Phase 2+3: check RSS-based memory pressure.
        let memory_pressure = self
            .memory_policy
            .as_ref()
            .map(|p| p.check())
            .unwrap_or(MemoryPressure::Normal);
        let memory_checkpoint = matches!(
            memory_pressure,
            MemoryPressure::Warning | MemoryPressure::Critical
        ) && self.checkpoint_enabled();
        let memory_stop = memory_pressure == MemoryPressure::Critical || internal_memory_stop;

        // Part of #3282: check disk usage against configured limit.
        let disk_stop = if let Some(disk_limit) = self.disk_limit_bytes {
            let disk_stats = FingerprintSet::stats(&*self.seen_fps);
            let estimated_disk_bytes = disk_stats.disk_count * 8;
            estimated_disk_bytes > disk_limit
        } else {
            false
        };

        let checkpoint_due = checkpoint_due || memory_checkpoint;

        if !liveness_due && !checkpoint_due && !memory_stop && !disk_stop {
            return PeriodicMaintenanceOutcome {
                periodic_result: None,
                checkpoint: None,
            };
        }

        if !internal_memory_stop {
            // Only print RSS-based messages if internal cap didn't already fire.
            if memory_pressure == MemoryPressure::Warning {
                let rss_mb = crate::memory::current_rss_bytes()
                    .map(|b| b / (1024 * 1024))
                    .unwrap_or(0);
                let limit_mb = self
                    .memory_policy
                    .as_ref()
                    .map(|p| p.limit_bytes() / (1024 * 1024))
                    .unwrap_or(0);
                eprintln!(
                    "Warning: memory usage ({rss_mb} MB) approaching limit ({limit_mb} MB). \
                     Breakdown: {}",
                    breakdown.format_diagnostic(),
                );
            } else if memory_pressure == MemoryPressure::Critical {
                let rss_mb = crate::memory::current_rss_bytes()
                    .map(|b| b / (1024 * 1024))
                    .unwrap_or(0);
                let limit_mb = self
                    .memory_policy
                    .as_ref()
                    .map(|p| p.limit_bytes() / (1024 * 1024))
                    .unwrap_or(0);
                eprintln!(
                    "Error: memory usage ({rss_mb} MB) exceeded critical threshold ({limit_mb} MB) \
                     — stopping exploration."
                );
                eprintln!("  Breakdown: {}", breakdown.format_diagnostic());
            }
        }

        self.barrier.suspend_all();

        let mut periodic_result = None;
        if liveness_due {
            let snapshot_stats =
                self.snapshot_runtime_stats(num_initial, detected_actions, detected_action_ids);
            let check_start = Instant::now();
            periodic_result = self.run_periodic_liveness(ctx, &snapshot_stats, promoted_properties);
            let finished_at = Instant::now();
            periodic_liveness.record_run(
                finished_at,
                current_states,
                finished_at.saturating_duration_since(check_start),
            );
            if periodic_result.is_some() {
                let _ = self.states_at_stop.set(snapshot_stats.states_found);
                self.stop_flag.store(true, Ordering::SeqCst);
            }
        }

        // Part of #2751: on critical memory pressure, set stop flag and
        // record LimitReached so finalize_check sees a clean result.
        if memory_stop {
            let _ = self.states_at_stop.set(current_states);
            self.stop_flag.store(true, Ordering::SeqCst);
            if periodic_result.is_none() {
                let snapshot =
                    self.snapshot_runtime_stats(num_initial, detected_actions, detected_action_ids);
                periodic_result = Some(CheckResult::LimitReached {
                    limit_type: LimitType::Memory,
                    stats: snapshot,
                });
            }
        }

        // Part of #3282: on disk limit exceeded, stop exploration gracefully.
        if disk_stop {
            if let Some(disk_limit) = self.disk_limit_bytes {
                let disk_stats = FingerprintSet::stats(&*self.seen_fps);
                let used =
                    crate::resource_budget::format_bytes(disk_stats.disk_count.saturating_mul(8));
                let limit = crate::resource_budget::format_bytes(disk_limit);
                eprintln!(
                    "Error: disk usage ({used}) exceeded limit ({limit}) \
                     — stopping exploration."
                );
            }
            let _ = self.states_at_stop.set(current_states);
            self.stop_flag.store(true, Ordering::SeqCst);
            if periodic_result.is_none() {
                let snapshot =
                    self.snapshot_runtime_stats(num_initial, detected_actions, detected_action_ids);
                periodic_result = Some(CheckResult::LimitReached {
                    limit_type: LimitType::Disk,
                    stats: snapshot,
                });
            }
        }

        let checkpoint = if checkpoint_due {
            Some(self.create_checkpoint())
        } else {
            None
        };

        self.barrier.resume_all();

        let checkpoint = match checkpoint {
            Some(Ok(checkpoint)) => Some(checkpoint),
            Some(Err(error)) => {
                eprintln!(
                    "Warning: parallel checkpoint creation failed: {error}. \
                     Exploration continues without checkpoint."
                );
                None
            }
            None => None,
        };

        PeriodicMaintenanceOutcome {
            periodic_result,
            checkpoint,
        }
    }
}
