// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal-result finalization and post-BFS completion.
//!
//! Contains the storage-error precedence gate (`finalize_terminal_result`),
//! the post-BFS orchestration (`finish_check_after_bfs`), and the deferred-
//! violation / depth-limit finalization (`finalize_bfs`).

use super::{
    print_enum_profile_stats, print_eval_profile_stats, CheckResult, LimitType, ModelChecker,
};
use crate::storage::FingerprintSet;

impl<'a> ModelChecker<'a> {
    /// Enforce storage-error precedence over any semantic outcome.
    ///
    /// If fingerprint storage has recorded errors (disk I/O failures, overflow),
    /// the storage error supersedes the candidate result. This ensures we never
    /// report a semantic outcome (deadlock, violation, success) from a run that
    /// already lost fingerprint-set soundness.
    ///
    /// Part of #1785: all terminal BFS outcomes must pass through this gate.
    pub(in crate::check) fn finalize_terminal_result(&self, candidate: CheckResult) -> CheckResult {
        if let Some(storage_error) = self.check_fingerprint_storage_errors() {
            storage_error
        } else {
            candidate
        }
    }

    /// Post-BFS finalization shared by both normal and resume paths.
    ///
    /// When `resume_mode` is `true`, liveness checking is rejected (not yet
    /// supported for checkpoint resume) instead of being run. All other
    /// post-BFS steps — profile stats, finalize_bfs, storage-error
    /// precedence, and POSTCONDITION — are identical.
    ///
    /// Part of #1812: eliminates structural duplication between
    /// `finish_check_after_bfs` and the former `finish_resume_after_bfs`.
    pub(in crate::check) fn finish_check_after_bfs(
        &mut self,
        depth_limit_reached: bool,
        resume_mode: bool,
    ) -> CheckResult {
        // Part of #2665: capture storage stats before any terminal return so
        // every CheckResult clone includes backend counters.
        self.stats.storage_stats = FingerprintSet::stats(&*self.state_storage.seen_fps);

        // Print detailed enumeration profile if enabled (has its own flag check)
        print_enum_profile_stats();
        // Part of #188: Print eval() call count for performance analysis
        print_eval_profile_stats();
        // Part of #4126: Report flat BFS adapter statistics.
        if let Some(ref adapter) = self.flat_bfs_adapter {
            adapter.report_stats();
        }
        #[cfg(feature = "jit")]
        self.log_jit_dispatch_summary();
        self.log_jit_verify_summary();
        // Finalize stats and check for early-exit conditions (depth limit, continue-on-error).
        // Part of #1785: route through finalize_terminal_result for storage error precedence.
        if let Some(result) = self.finalize_bfs(depth_limit_reached) {
            return self.finalize_terminal_result(result);
        }

        // Storage overflow or disk lookup I/O failures make exploration incomplete.
        // Fail before liveness/postcondition so we never report a semantic outcome
        // from a run that already lost fingerprint-set soundness.
        if let Some(result) = self.check_fingerprint_storage_errors() {
            return result;
        }

        if resume_mode {
            // Part of #1793: fail loudly instead of returning Success when temporal
            // properties were not checked on a resumed run.
            //
            // Part of #1812: after #3175/#3205, fingerprint-only mode supports
            // liveness during fresh BFS runs, but resume still does not persist
            // the BFS-time liveness caches needed to replay temporal checks.
            // Resumed runs must therefore reject unchecked temporal properties in
            // both full-state and fingerprint-only modes.
            let has_liveness_properties = self.config.has_liveness_properties();
            let skip_liveness_flag = super::debug::skip_liveness();

            if has_liveness_properties && !skip_liveness_flag {
                return self.finalize_terminal_result(CheckResult::from_error(
                    crate::LivenessCheckError::Generic(format!(
                        "Checkpoint resume does not yet support PROPERTY/liveness checking \
                         in full-state or fingerprint-only mode. Temporal properties were NOT checked: {}. \
                         Re-run without --resume to verify liveness.",
                        self.config.properties.join(", ")
                    ))
                    .into(),
                    self.stats.clone(),
                ));
            }
        } else {
            // Check liveness properties (temporal formulas) after safety checking passes.
            if let Some(result) = self.run_liveness_checking(false) {
                return self.finalize_terminal_result(result);
            }
        }

        // Evaluate POSTCONDITION after model checking completes (TLC parity).
        if let Some(result) = self.check_postcondition() {
            return self.finalize_terminal_result(result);
        }

        self.finalize_terminal_result(CheckResult::Success(self.stats.clone()))
    }

    // Debug successor helpers (debug_successor_flags, debug_print_state_line,
    // debug_log_successor_details) are in run_debug.rs.

    /// Finalize BFS exploration: update stats, check depth limit, and return deferred violations.
    pub(in crate::check) fn finalize_bfs(
        &mut self,
        depth_limit_reached: bool,
    ) -> Option<CheckResult> {
        self.stats.states_found = self.states_count();
        self.update_coverage_totals();

        // Populate symmetry reduction statistics into CheckStats.
        self.populate_symmetry_stats();

        // Part of #2841: copy FP collision counters to stats for CLI reporting.
        self.stats.fp_dedup_collisions = self.debug.seen_tlc_fp_dedup_collisions;
        self.stats.internal_fp_collisions = self.debug.internal_fp_collisions;

        // Copy collision detection stats to CheckStats.
        if let Some(ref detector) = self.collision_detector {
            self.stats.collision_check_mode = detector.mode();
            self.stats.collision_check_stats = detector.stats();
        }

        // Part of #3850: log tiered JIT summary at end of BFS when promotions occurred.
        // Part of #3910: detailed `--show-tiers` report when TLA2_SHOW_TIERS=1.
        #[cfg(feature = "jit")]
        if let Some(ref manager) = self.tier_manager {
            let summary = manager.tier_summary();
            if summary.tier1 > 0 || summary.tier2 > 0 {
                eprintln!("[jit] Tier summary: {summary}");
            }
            // Full tier report when `--show-tiers` / TLA2_SHOW_TIERS=1 is set.
            if {
                static SHOW_TIERS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                *SHOW_TIERS.get_or_init(|| std::env::var("TLA2_SHOW_TIERS").is_ok_and(|v| v == "1"))
            } {
                eprint!("{}", self.format_tier_report());
            }
        }
        // Always print next-state dispatch counters when stats mode is on.
        #[cfg(feature = "jit")]
        if {
            static VM_STATS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *VM_STATS.get_or_init(|| std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1"))
        } {
            let ns = &self.next_state_dispatch;
            if ns.total > 0 {
                eprintln!(
                    "[jit] Next-state dispatch: hits={}, fallbacks={}, not_compiled={}, errors={}, total={}",
                    ns.jit_hit, ns.jit_fallback, ns.jit_not_compiled, ns.jit_error, ns.total,
                );
            }
        }

        // Part of #3993: Populate POR reduction statistics into CheckStats
        // and report when reduction was active.
        if let Some(ref independence) = self.por.independence {
            let stats = &self.por.stats;
            // Part of #3993 Phase 11: independence counts now always available.
            let indep_pairs = independence.count_independent_pairs();
            let total_pairs = independence.total_pairs();

            self.stats.por_reduction = crate::check::api::PorReductionStats {
                action_count: self.stats.detected_actions.len(),
                independent_pairs: indep_pairs,
                total_pairs,
                states_reduced: stats.reductions,
                states_processed: stats.total_states,
                actions_skipped: stats.actions_skipped,
                auto_detected: !self.config.por_enabled,
            };

            // Part of #3993 Phase 11: emit POR diagnostic summary with action names.
            if indep_pairs > 0 || stats.total_states > 0 {
                eprintln!(
                    "{}",
                    independence.diagnostic_summary(&self.stats.detected_actions)
                );
            }
            if stats.total_states > 0 {
                let pct = 100.0 * stats.reductions as f64 / stats.total_states as f64;
                eprintln!(
                    "POR: {}/{} states reduced ({:.1}%), {} actions skipped",
                    stats.reductions, stats.total_states, pct, stats.actions_skipped,
                );
            }
        }

        // If we skipped states due to depth limit, report that
        if depth_limit_reached {
            return Some(CheckResult::LimitReached {
                limit_type: LimitType::Depth,
                stats: self.stats.clone(),
            });
        }

        // Part of #595: If we recorded a violation in continue_on_error mode, return it now
        // with final stats (full state space was explored).
        if let Some((property, fp)) = self.exploration.first_action_property_violation.take() {
            let trace = self.reconstruct_trace(fp);
            return Some(CheckResult::PropertyViolation {
                property,
                kind: crate::check::api::PropertyViolationKind::ActionLevel,
                trace,
                stats: self.stats.clone(),
            });
        }

        if let Some((invariant, fp)) = self.exploration.first_violation.take() {
            let trace = self.reconstruct_trace(fp);
            if self
                .compiled
                .state_property_violation_names
                .contains(&invariant)
            {
                return Some(CheckResult::PropertyViolation {
                    property: invariant,
                    kind: crate::check::api::PropertyViolationKind::StateLevel,
                    trace,
                    stats: self.stats.clone(),
                });
            }
            return Some(CheckResult::InvariantViolation {
                invariant,
                trace,
                stats: self.stats.clone(),
            });
        }

        None
    }
}

#[cfg(test)]
#[path = "run_finalize_tests.rs"]
mod run_finalize_tests;
