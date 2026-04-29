// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-collection terminal synthesis: worker/progress joins, final stats,
//! fingerprint-storage precedence, and terminal-result resolution.
//!
//! Extracted from `finalize.rs` for file size compliance (#3522).

use super::super::terminal_outcome::{merge_worker_outcome, TerminalOutcome};
use super::super::*;
use super::collect::CollectedFinalizeState;
use crate::{EvalCheckError, InfraCheckError, RuntimeCheckError};

/// Check if `--show-tiers` / `TLA2_SHOW_TIERS=1` is enabled.
/// Cached via `OnceLock` (Part of #4114).
fn show_tiers_enabled() -> bool {
    static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("TLA2_SHOW_TIERS").is_ok_and(|v| v == "1"))
}

impl ParallelChecker {
    /// Join worker and progress threads, build final stats, and resolve the
    /// terminal `CheckResult`.
    ///
    /// Precedence: Error > Violation > Deadlock > (DepthLimit > DeferredViolation > Limit)
    /// then post-BFS liveness, POSTCONDITION, success.
    pub(super) fn join_and_resolve_terminal(
        &self,
        collected: CollectedFinalizeState,
        handles: Vec<std::thread::JoinHandle<()>>,
        progress_handle: Option<std::thread::JoinHandle<()>>,
        ctx: &mut tla_eval::EvalCtx,
        num_initial: usize,
        detected_actions: Vec<String>,
        detected_action_ids: Vec<String>,
        promoted_properties: Vec<String>,
        state_property_violation_names: Vec<String>,
    ) -> CheckResult {
        let CollectedFinalizeState {
            total_stats,
            mut outcome,
            periodic_result,
        } = collected;

        // Merge join errors (thread panics) into the collected outcome.
        // Thread panics are treated as Error-level outcomes.
        let mut join_error: Option<CheckError> = None;

        // Wait for all workers to finish
        for (worker_id, handle) in handles.into_iter().enumerate() {
            if let Err(payload) = handle.join() {
                let error: CheckError = InfraCheckError::WorkerThreadPanicked {
                    worker_id,
                    message: panic_payload_message(payload.as_ref()),
                }
                .into();
                if join_error.is_none() {
                    join_error = Some(error);
                } else {
                    eprintln!("WARNING: additional worker thread panic: {error}");
                }
            }
        }

        // NOTE: Value interner unfreeze is handled by the caller
        // (run_check_inner) to avoid mutating process-global state inside
        // finalize_check(). Unit tests call finalize_check() directly in
        // parallel; moving unfreeze here caused FROZEN_SNAPSHOT mutex
        // poisoning when the interner_cleanup test ran concurrently.

        // Stop and wait for progress thread
        if let Some(handle) = progress_handle {
            self.stop_flag.store(true, Ordering::SeqCst);
            if let Err(payload) = handle.join() {
                let error: CheckError = InfraCheckError::ProgressThreadPanicked {
                    message: panic_payload_message(payload.as_ref()),
                }
                .into();
                if join_error.is_none() {
                    join_error = Some(error);
                } else {
                    eprintln!("WARNING: additional progress thread panic: {error}");
                }
            }
        }

        // Part of #3910: Log tier summary after all threads have completed.
        if let Some(tier) = self.tier_state.get() {
            let summary = tier.tier_summary();
            if summary.tier1 > 0 || summary.tier2 > 0 {
                eprintln!("[jit] Parallel tier summary: {summary}");
            }
            // Part of #3932: Detailed per-action tier report when --show-tiers is set.
            if show_tiers_enabled() {
                tier.print_tier_report();
            }
        }

        if let Some(error) = join_error {
            // Merge join error into outcome using the same precedence rules.
            let incoming = TerminalOutcome::Error(error);
            outcome = Some(match outcome {
                None => incoming,
                Some(current) => merge_worker_outcome(current, incoming),
            });
        }

        let final_stats = CheckStats {
            // Part of #1906/#2309: use the snapshot taken at the moment of the
            // first stop event (violation/error/deadlock). If no snapshot was
            // taken (clean exploration completed), fall back to the post-
            // termination count. OnceLock distinguishes `Some(0)` (valid zero-
            // count snapshot) from `None` (no snapshot taken), fixing the #2309
            // sentinel overload where count==0 was indistinguishable from "unset".
            states_found: self
                .states_at_stop
                .get()
                .copied()
                .unwrap_or_else(|| self.states_count()),
            initial_states: num_initial,
            max_queue_depth: self.max_queue_depth.load(Ordering::SeqCst),
            transitions: total_stats.transitions,
            max_depth: self.max_depth.load(Ordering::SeqCst),
            detected_actions,
            detected_action_ids,
            coverage: None,
            phantom_dequeues: 0,
            suppressed_guard_errors: crate::guard_error_stats::take_and_reset(),
            trace_reconstructions: 0, // Parallel workers don't track this yet
            fp_dedup_collisions: self.fp_dedup_collisions(),
            internal_fp_collisions: self.internal_fp_collisions(),
            // Part of #2665: capture storage backend counters.
            storage_stats: FingerprintSet::stats(&*self.seen_fps),
            collision_check_mode: Default::default(),
            collision_check_stats: Default::default(),
            symmetry_reduction: Default::default(),
            por_reduction: Default::default(),
        };

        // Fingerprint storage errors take absolute precedence over all other
        // outcomes. Storage errors mean the fingerprint set lost insertions
        // (I/O failures, overflow), making the exploration unsound — we cannot
        // trust any semantic result (violation, deadlock, limit, or success)
        // produced from an incomplete state space.
        //
        // Part of #1800: parity with the serial path, where every terminal
        // outcome routes through `finalize_terminal_result` which checks
        // `check_fingerprint_storage_errors()` first.
        // Part of #2056: use the shared check_fingerprint_errors() helper
        // instead of inline construction to keep .max(1) floor logic in one place.
        if let Some(error) = crate::checker_ops::check_fingerprint_errors(self.seen_fps.as_ref()) {
            return check_error_to_result(error, &final_stats);
        }

        // Resolve worker-collected terminal outcomes.
        //
        // Precedence: Error > Violation > Deadlock > (DepthLimit > DeferredViolation > Limit)
        //
        // Error/Violation/Deadlock return immediately. Limit outcomes require
        // additional checks: depth_limit_reached (shared atomic) takes precedence
        // over worker-reported limits, and deferred violations (continue-on-error
        // mode) take precedence over non-depth limits. This matches the serial
        // finalize_bfs ordering.
        let mut worker_limit: Option<LimitType> = None;
        match outcome {
            Some(TerminalOutcome::Error(error)) => {
                return check_error_to_result(error, &final_stats);
            }
            Some(TerminalOutcome::Violation {
                invariant,
                state_fp,
            }) => {
                // Part of #2470: use reconstruct_trace_with_labels for action label parity.
                let trace = self.reconstruct_trace_with_labels(state_fp, ctx);
                if state_property_violation_names.contains(&invariant) {
                    return CheckResult::PropertyViolation {
                        property: invariant,
                        kind: crate::check::PropertyViolationKind::StateLevel,
                        trace,
                        stats: final_stats,
                    };
                }
                return CheckResult::InvariantViolation {
                    invariant,
                    trace,
                    stats: final_stats,
                };
            }
            Some(TerminalOutcome::PropertyActionViolation { property, state_fp }) => {
                let trace = self.reconstruct_trace_with_labels(state_fp, ctx);
                return CheckResult::PropertyViolation {
                    property,
                    kind: crate::check::PropertyViolationKind::ActionLevel,
                    trace,
                    stats: final_stats,
                };
            }
            Some(TerminalOutcome::Deadlock { state_fp }) => {
                let trace = self.reconstruct_trace_with_labels(state_fp, ctx);
                return CheckResult::Deadlock {
                    trace,
                    stats: final_stats,
                };
            }
            Some(TerminalOutcome::Limit(limit_type)) => {
                worker_limit = Some(limit_type);
            }
            None => {}
        }

        // No worker-reported terminal outcome. Check post-exploration conditions.

        // Part of #2216: Depth limit from shared atomic flag (workers continued
        // processing after setting it, matching serial BFS semantics).
        if self.depth_limit_reached.load(Ordering::Relaxed) {
            return CheckResult::LimitReached {
                limit_type: LimitType::Depth,
                stats: final_stats,
            };
        }

        if let Some((property, state_fp)) = self.first_action_property_violation.get().cloned() {
            let trace = self.reconstruct_trace_with_labels(state_fp, ctx);
            if !trace.is_empty() {
                let _ = self.first_violation_trace.set(trace.states.clone());
            }
            return CheckResult::PropertyViolation {
                property,
                kind: crate::check::PropertyViolationKind::ActionLevel,
                trace,
                stats: final_stats,
            };
        }

        // Deferred violations from continue_on_error mode (from self.first_violation OnceLock).
        if let Some((invariant, state_fp)) = self.first_violation.get().cloned() {
            let trace = self.reconstruct_trace_with_labels(state_fp, ctx);
            if !trace.is_empty() {
                let _ = self.first_violation_trace.set(trace.states.clone());
            }
            if state_property_violation_names.contains(&invariant) {
                return CheckResult::PropertyViolation {
                    property: invariant,
                    kind: crate::check::PropertyViolationKind::StateLevel,
                    trace,
                    stats: final_stats,
                };
            }
            return CheckResult::InvariantViolation {
                invariant,
                trace,
                stats: final_stats,
            };
        }

        // Main-thread periodic liveness runs while workers are still active, but
        // worker-reported errors/violations/deadlocks still take precedence.
        if let Some(result) = periodic_result {
            return result;
        }

        if let Some(limit_type) = worker_limit {
            return CheckResult::LimitReached {
                limit_type,
                stats: final_stats,
            };
        }

        // Part of #2740: Run liveness checking after BFS completes successfully.
        if let Some(result) = self.run_post_bfs_liveness(ctx, &final_stats, &promoted_properties) {
            return result;
        }

        // Evaluate POSTCONDITION after model checking completes (TLC parity).
        if let Some(ref postcondition_name) = self.config.postcondition {
            let runtime_stats = match crate::checker_ops::final_bfs_runtime_stats(&final_stats) {
                Ok(stats) => stats,
                Err(error) => {
                    return check_error_to_result(error, &final_stats);
                }
            };
            ctx.set_tlc_runtime_stats(Some(runtime_stats));
            ctx.set_tlc_level(runtime_stats.diameter as u32);
            // Part of #3458: Clear eval-scope caches before postcondition evaluation.
            crate::eval::clear_for_eval_scope_boundary();
            match ctx.eval_op(postcondition_name) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) | Ok(_) => {
                    return check_error_to_result(
                        RuntimeCheckError::PostconditionFalse {
                            operator: postcondition_name.clone(),
                        }
                        .into(),
                        &final_stats,
                    );
                }
                Err(e) => {
                    return check_error_to_result(EvalCheckError::Eval(e).into(), &final_stats);
                }
            }
        }

        CheckResult::Success(final_stats)
    }
}
