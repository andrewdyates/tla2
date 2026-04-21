// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Active-run supervision: progress-thread spawn and worker-result collection.
//!
//! Extracted from `finalize.rs` for file size compliance (#3522).

use super::super::terminal_outcome::{aggregate_stats, merge_worker_outcome, TerminalOutcome};
use super::super::*;
use crossbeam_channel::RecvTimeoutError;

/// Compact intermediate state returned by `collect_worker_results`.
pub(super) struct CollectedFinalizeState {
    pub(super) total_stats: WorkerStats,
    pub(super) outcome: Option<TerminalOutcome>,
    pub(super) periodic_result: Option<CheckResult>,
}

impl ParallelChecker {
    /// Spawn the progress-reporting thread (and capacity-warning loop).
    /// Returns `None` if no progress callback is set or interval is zero.
    pub(super) fn spawn_progress_reporter(
        &self,
        _start_time: std::time::Instant,
    ) -> Option<std::thread::JoinHandle<()>> {
        if let Some(ref callback) = self.progress_callback {
            if self.progress_interval_ms > 0 {
                let callback = Arc::clone(callback);
                let stop_flag = Arc::clone(&self.stop_flag);
                let seen = Arc::clone(&self.seen);
                let seen_fps = Arc::clone(&self.seen_fps);
                let max_depth = Arc::clone(&self.max_depth);
                let max_queue_depth = Arc::clone(&self.max_queue_depth);
                let total_transitions = Arc::clone(&self.total_transitions);
                let interval = Duration::from_millis(self.progress_interval_ms);
                let start_time = Instant::now();
                let store_full_states = self.store_full_states;
                // Track capacity status for warning suppression
                let last_capacity_status = Arc::new(AtomicU8::new(CAPACITY_NORMAL));

                // Part of #3910: Clone tier_state for periodic promotion checks.
                let tier_state = self.tier_state.get().map(Arc::clone);

                Some(thread::spawn(move || {
                    while !stop_flag.load(Ordering::Relaxed) {
                        thread::sleep(interval);
                        if stop_flag.load(Ordering::Relaxed) {
                            break;
                        }
                        let states_found = if store_full_states {
                            seen.len()
                        } else {
                            seen_fps.len()
                        };
                        let elapsed_secs = start_time.elapsed().as_secs_f64();
                        let states_per_sec = if elapsed_secs > 0.0 {
                            states_found as f64 / elapsed_secs
                        } else {
                            0.0
                        };
                        let progress = Progress {
                            states_found,
                            current_depth: max_depth.load(Ordering::Relaxed),
                            queue_size: max_queue_depth.load(Ordering::Relaxed),
                            transitions: total_transitions.load(Ordering::Relaxed),
                            elapsed_secs,
                            states_per_sec,
                            memory_usage_bytes: crate::memory::current_rss_bytes()
                                .map(|b| b as u64),
                            ..Default::default()
                        };
                        callback(&progress);

                        // Check capacity warnings at progress intervals
                        check_and_warn_capacity(seen_fps.as_ref(), &last_capacity_status);

                        // Part of #3910: Check for tier promotions at each progress interval.
                        if let Some(ref tier) = tier_state {
                            tier.check_promotions();
                        }
                    }
                }))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Collect worker results using merge_worker_outcome for precedence-correct
    /// reduction (Part of #1433 Step 4).
    pub(super) fn collect_worker_results(
        &self,
        result_rx: crossbeam_channel::Receiver<WorkerResult>,
        ctx: &mut tla_eval::EvalCtx,
        num_initial: usize,
        detected_actions: &[String],
        detected_action_ids: &[String],
        promoted_properties: &[String],
        start_time: std::time::Instant,
    ) -> CollectedFinalizeState {
        let mut total_stats = WorkerStats::default();
        let mut outcome: Option<TerminalOutcome> = None;
        let mut periodic_result: Option<CheckResult> = None;
        let needs_periodic_loop = self.checkpoint_enabled()
            || self.periodic_liveness_enabled()
            || self.memory_policy.is_some()
            || self.disk_limit_bytes.is_some();

        if needs_periodic_loop {
            let mut last_checkpoint = start_time;
            let mut periodic_liveness = self.periodic_liveness.clone();
            let poll_interval = Duration::from_secs(1);
            loop {
                match result_rx.recv_timeout(poll_interval) {
                    Ok(result) => {
                        let (stats, terminal) = self.classify_worker_result(result);
                        aggregate_stats(&mut total_stats, &stats);
                        if let Some(incoming) = terminal {
                            outcome = Some(match outcome {
                                None => incoming,
                                Some(current) => merge_worker_outcome(current, incoming),
                            });
                        }
                    }
                    Err(RecvTimeoutError::Timeout) => {
                        if self.stop_flag.load(Ordering::Relaxed) || periodic_result.is_some() {
                            continue;
                        }
                        if self.work_remaining.load(Ordering::Acquire) == 0
                            && self.active_workers.load(Ordering::Acquire) == 0
                        {
                            continue;
                        }

                        let checkpoint_due = self.checkpoint_enabled()
                            && last_checkpoint.elapsed() >= self.checkpoint_interval;
                        let maintenance = self.run_periodic_maintenance(
                            ctx,
                            num_initial,
                            detected_actions,
                            detected_action_ids,
                            promoted_properties,
                            start_time,
                            &mut periodic_liveness,
                            checkpoint_due,
                        );
                        if checkpoint_due || maintenance.checkpoint.is_some() {
                            last_checkpoint = Instant::now();
                        }
                        if periodic_result.is_none() {
                            periodic_result = maintenance.periodic_result;
                        }
                        if let Some(checkpoint) = maintenance.checkpoint {
                            if let Some(dir) = self.checkpoint_dir.as_ref() {
                                if let Err(error) = checkpoint.save(dir) {
                                    eprintln!(
                                        "Warning: parallel checkpoint save failed: {error}. \
                                         Exploration continues without checkpoint."
                                    );
                                }
                            }
                        }
                    }
                    Err(RecvTimeoutError::Disconnected) => break,
                }
            }
        } else {
            for result in result_rx {
                let (stats, terminal) = self.classify_worker_result(result);
                aggregate_stats(&mut total_stats, &stats);
                if let Some(incoming) = terminal {
                    outcome = Some(match outcome {
                        None => incoming,
                        Some(current) => merge_worker_outcome(current, incoming),
                    });
                }
            }
        }

        CollectedFinalizeState {
            total_stats,
            outcome,
            periodic_result,
        }
    }
}
