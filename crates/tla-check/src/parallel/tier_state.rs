// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared tiered JIT state for parallel model checking.
//!
//! Provides thread-safe action evaluation counters and a `TierManager`
//! wrapper that the main coordination thread uses for promotion checks
//! while workers atomically increment per-action evaluation counts.
//!
//! Part of #3910: Wire TierManager into parallel BFS loop.

use std::fmt::Write as _;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

/// Thread-safe wrapper around `TierManager` and per-action atomic counters.
///
/// Workers call [`record_action_eval`] on the hot path (one relaxed atomic
/// add per successor batch — negligible overhead). The main coordination
/// thread calls [`check_promotions`] periodically (at progress intervals)
/// to detect tier transitions and log them.
pub(crate) struct SharedTierState {
    /// Per-action evaluation counts (indexed by action_id).
    /// Workers increment these atomically during successor generation.
    action_eval_counts: Vec<AtomicU64>,
    /// Per-action total successor counts for branching factor computation.
    action_succ_totals: Vec<AtomicU64>,
    /// The tier manager itself — accessed only by the coordination thread
    /// during periodic promotion checks. Mutex is uncontended in practice
    /// because only the main thread calls `check_promotions`.
    manager: Mutex<tla_jit::TierManager>,
    /// Cached action labels for diagnostic messages.
    /// `None` entry = monolithic "Next".
    action_labels: Vec<Option<String>>,
    /// JIT-compiled next-state cache, set once at startup.
    /// Workers read this concurrently after tier promotion to evaluate
    /// successor states via JIT instead of the interpreter.
    jit_next_state_cache: OnceLock<super::SharedJitNextStateCache>,
    /// Accumulated next-state dispatch counters for end-of-run logging.
    /// Only the main thread reads these (during finalization); workers
    /// update them via `record_next_state_dispatch`.
    next_state_jit_hits: AtomicU64,
    next_state_jit_fallbacks: AtomicU64,
    next_state_jit_not_compiled: AtomicU64,
    next_state_jit_errors: AtomicU64,
    next_state_jit_total: AtomicU64,
    /// Accumulated promotion events, recorded by `check_promotions()`.
    /// Only the coordination thread appends; read during `print_tier_report()`.
    promotion_history: Mutex<Vec<tla_jit::TierPromotion>>,
}

impl SharedTierState {
    /// Create a new shared tier state for the given action count.
    ///
    /// `action_labels` provides human-readable names for promotion log messages.
    /// Pass `None` entries for unnamed/monolithic actions.
    pub(crate) fn new(action_count: usize, action_labels: Vec<Option<String>>) -> Self {
        let mut manager = tla_jit::TierManager::new(action_count);
        // Mark all actions as JIT-eligible by default. The bytecode lowerer
        // will filter out actions that cannot be compiled when promotion fires.
        for i in 0..action_count {
            manager.set_eligible(i);
        }

        let action_eval_counts = (0..action_count)
            .map(|_| AtomicU64::new(0))
            .collect();
        let action_succ_totals = (0..action_count)
            .map(|_| AtomicU64::new(0))
            .collect();

        SharedTierState {
            action_eval_counts,
            action_succ_totals,
            manager: Mutex::new(manager),
            action_labels,
            jit_next_state_cache: OnceLock::new(),
            next_state_jit_hits: AtomicU64::new(0),
            next_state_jit_fallbacks: AtomicU64::new(0),
            next_state_jit_not_compiled: AtomicU64::new(0),
            next_state_jit_errors: AtomicU64::new(0),
            next_state_jit_total: AtomicU64::new(0),
            promotion_history: Mutex::new(Vec::new()),
        }
    }

    /// Set the JIT next-state cache (called once during startup).
    ///
    /// After this is set, workers can use `jit_next_state_cache()` to
    /// evaluate actions via JIT instead of the interpreter.
    pub(crate) fn set_jit_next_state_cache(&self, cache: super::SharedJitNextStateCache) {
        let _ = self.jit_next_state_cache.set(cache);
    }

    /// Get the JIT next-state cache, if available.
    pub(crate) fn jit_next_state_cache(&self) -> Option<&tla_jit::JitNextStateCache> {
        self.jit_next_state_cache.get().map(|arc| arc.as_ref())
    }

    /// Check whether the monolithic Next action (action_id=0) has been
    /// promoted to at least Tier 1 (basic JIT).
    ///
    /// Workers call this on the hot path to decide whether to attempt
    /// JIT evaluation for successor generation.
    pub(crate) fn is_promoted_to_jit(&self, action_id: usize) -> bool {
        let manager = self
            .manager
            .lock()
            .expect("invariant: SharedTierState manager mutex should not be poisoned");
        manager.current_tier(action_id) >= tla_jit::CompilationTier::Tier1
    }

    /// Enable type profiling on the tier manager for Tier 2 specialization.
    ///
    /// Called once after the state variable count is known. The profiler
    /// collects runtime types during BFS warmup and produces a specialization
    /// plan on Tier 2 promotion.
    ///
    /// Part of #3989: speculative type specialization.
    pub(crate) fn enable_type_profiling(&self, var_count: usize) {
        let mut manager = self
            .manager
            .lock()
            .expect("invariant: SharedTierState manager mutex should not be poisoned");
        manager.enable_type_profiling(var_count);
    }

    /// Observe the runtime types of state variable values for type profiling.
    ///
    /// Called from worker threads during BFS. Acquires the manager lock to
    /// feed type observations to the profiler. After the warmup threshold is
    /// reached, the profiler freezes and this method returns immediately
    /// (the lock is still acquired but the fast `type_profile_stable()` check
    /// exits quickly).
    ///
    /// Part of #3989: speculative type specialization.
    pub(crate) fn observe_state_types(&self, types: &[tla_jit::SpecType]) {
        let mut manager = self
            .manager
            .lock()
            .expect("invariant: SharedTierState manager mutex should not be poisoned");
        if manager.type_profile_stable() {
            return;
        }
        let stabilized = manager.observe_state_types(types);
        if stabilized {
            if let Some(profile) = manager.type_profile() {
                let mono_types = profile.monomorphic_types();
                eprintln!(
                    "[jit] Type profile stabilized after {} states: {:?}",
                    profile.total_states(),
                    mono_types,
                );
            }
        }
    }

    /// Record an action evaluation from a worker thread.
    ///
    /// Called on the BFS hot path after successor generation completes for
    /// a state. Uses `Relaxed` ordering — promotion checks tolerate stale
    /// counts (they just fire one progress interval later).
    #[inline]
    pub(crate) fn record_action_eval(&self, action_id: usize, successor_count: u64) {
        if let Some(counter) = self.action_eval_counts.get(action_id) {
            counter.fetch_add(1, Ordering::Relaxed);
        }
        if let Some(counter) = self.action_succ_totals.get(action_id) {
            counter.fetch_add(successor_count, Ordering::Relaxed);
        }
    }

    /// Record next-state JIT dispatch counters from a worker thread.
    ///
    /// Called after JIT evaluation of successor states. Uses `Relaxed`
    /// ordering — counters are only read at end-of-run for diagnostics.
    #[inline]
    pub(crate) fn record_next_state_dispatch(
        &self,
        counters: &tla_jit::NextStateDispatchCounters,
    ) {
        self.next_state_jit_hits
            .fetch_add(counters.jit_hit as u64, Ordering::Relaxed);
        self.next_state_jit_fallbacks
            .fetch_add(counters.jit_fallback as u64, Ordering::Relaxed);
        self.next_state_jit_not_compiled
            .fetch_add(counters.jit_not_compiled as u64, Ordering::Relaxed);
        self.next_state_jit_errors
            .fetch_add(counters.jit_error as u64, Ordering::Relaxed);
        self.next_state_jit_total
            .fetch_add(counters.total as u64, Ordering::Relaxed);
    }

    /// Check for tier promotions and log any transitions.
    ///
    /// Called by the main coordination thread at progress intervals.
    /// Reads atomic counters with `Relaxed` ordering (approximate is fine)
    /// and forwards them to `TierManager::promotion_check`.
    pub(crate) fn check_promotions(&self) {
        let mut manager = self
            .manager
            .lock()
            .expect("invariant: SharedTierState manager mutex should not be poisoned");

        let action_count = manager.action_count();
        let profiles: Vec<tla_jit::ActionProfile> = (0..action_count)
            .map(|i| {
                let evals = self
                    .action_eval_counts
                    .get(i)
                    .map_or(0, |c| c.load(Ordering::Relaxed));
                let total_succ = self
                    .action_succ_totals
                    .get(i)
                    .map_or(0, |c| c.load(Ordering::Relaxed));
                let bf = if evals > 0 {
                    total_succ as f64 / evals as f64
                } else {
                    0.0
                };
                tla_jit::ActionProfile {
                    times_evaluated: evals,
                    branching_factor: bf,
                    jit_eligible: true,
                }
            })
            .collect();

        let promotions = manager.promotion_check(&profiles);
        let show_tiers = {
            static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *CACHED.get_or_init(|| std::env::var("TLA2_SHOW_TIERS").is_ok_and(|v| v == "1"))
        };
        for promo in &promotions {
            let action_label = self
                .action_labels
                .get(promo.action_id)
                .and_then(|l| l.as_deref())
                .unwrap_or("Next");
            // Part of #3989: include specialization info for Tier 2 promotions.
            let spec_info = promo.specialization_plan.as_ref().map(|plan| {
                format!(
                    " [specialized: {} vars, {}i/{}b, est. {:.2}x]",
                    plan.specialized_var_count(),
                    plan.int_var_count(),
                    plan.bool_var_count(),
                    plan.expected_speedup_factor,
                )
            });
            let spec_suffix = spec_info.as_deref().unwrap_or("");
            if show_tiers {
                // Part of #3932: Real-time promotion events with --show-tiers.
                eprintln!(
                    "[tier] Action '{}' promoted to {} after {} invocations (bf={:.1}){}",
                    action_label,
                    promo.new_tier,
                    promo.evaluations_at_promotion,
                    promo.branching_factor,
                    spec_suffix,
                );
            } else {
                eprintln!(
                    "[jit] Action '{}': {} -> {} at {} evals (bf={:.1}){}",
                    action_label,
                    promo.old_tier,
                    promo.new_tier,
                    promo.evaluations_at_promotion,
                    promo.branching_factor,
                    spec_suffix,
                );
            }
        }
        // Stash promotions for end-of-run reporting.
        if !promotions.is_empty() {
            let mut history = self
                .promotion_history
                .lock()
                .expect("invariant: promotion_history mutex should not be poisoned");
            history.extend(promotions);
        }
    }

    /// Return a tier summary for end-of-run logging.
    pub(crate) fn tier_summary(&self) -> tla_jit::TierSummary {
        self.manager
            .lock()
            .expect("invariant: SharedTierState manager mutex should not be poisoned")
            .tier_summary()
    }

    /// Return accumulated next-state dispatch counters for end-of-run logging.
    pub(crate) fn next_state_dispatch_summary(&self) -> tla_jit::NextStateDispatchCounters {
        tla_jit::NextStateDispatchCounters {
            jit_hit: self.next_state_jit_hits.load(Ordering::Relaxed) as usize,
            jit_fallback: self.next_state_jit_fallbacks.load(Ordering::Relaxed) as usize,
            jit_not_compiled: self
                .next_state_jit_not_compiled
                .load(Ordering::Relaxed) as usize,
            jit_error: self.next_state_jit_errors.load(Ordering::Relaxed) as usize,
            total: self.next_state_jit_total.load(Ordering::Relaxed) as usize,
        }
    }

    /// Print detailed per-action tier report when `--show-tiers` is set.
    ///
    /// Part of #3932: `--show-tiers` CLI diagnostic.
    pub(crate) fn print_tier_report(&self) {
        eprint!("{}", self.format_tier_report());
    }

    /// Format the tier report as a `String` (for testability).
    ///
    /// Returns a multi-line report showing per-action compilation tier,
    /// evaluation count, branching factor, and promotion transitions, plus
    /// JIT dispatch statistics and a summary line.
    ///
    /// Part of #3932.
    pub(crate) fn format_tier_report(&self) -> String {
        let manager = self
            .manager
            .lock()
            .expect("invariant: SharedTierState manager mutex should not be poisoned");
        let action_count = manager.action_count();
        let dispatch = self.next_state_dispatch_summary();
        let summary = manager.tier_summary();
        let history = self
            .promotion_history
            .lock()
            .expect("invariant: promotion_history mutex should not be poisoned");

        // Count promotions per action.
        let mut per_action_promotions = vec![0usize; action_count];
        for promo in history.iter() {
            if promo.action_id < action_count {
                per_action_promotions[promo.action_id] += 1;
            }
        }

        let mut out = String::new();
        let _ = writeln!(out);
        let _ = writeln!(out, "=== Tier Compilation Report ===");
        let _ = writeln!(
            out,
            "{:<30} {:>18} {:>12} {:>10} {:>12}",
            "Action", "Tier", "Evals", "Avg BF", "Promotions"
        );
        let _ = writeln!(out, "{}", "-".repeat(86));

        for i in 0..action_count {
            let label = self
                .action_labels
                .get(i)
                .and_then(|l| l.as_deref())
                .unwrap_or("Next");
            let tier = manager.current_tier(i);
            let evals = self
                .action_eval_counts
                .get(i)
                .map_or(0, |c| c.load(Ordering::Relaxed));
            let total_succ = self
                .action_succ_totals
                .get(i)
                .map_or(0, |c| c.load(Ordering::Relaxed));
            let bf = if evals > 0 {
                total_succ as f64 / evals as f64
            } else {
                0.0
            };
            let promos = per_action_promotions.get(i).copied().unwrap_or(0);
            let _ = writeln!(
                out,
                "{:<30} {:>18} {:>12} {:>10.1} {:>12}",
                truncate_label(label, 30),
                tier,
                evals,
                bf,
                promos,
            );
        }

        // Promotion event log.
        if !history.is_empty() {
            let _ = writeln!(out);
            let _ = writeln!(out, "Promotion events:");
            for promo in history.iter() {
                let label = self
                    .action_labels
                    .get(promo.action_id)
                    .and_then(|l| l.as_deref())
                    .unwrap_or("Next");
                let _ = writeln!(
                    out,
                    "  '{}': {} -> {} at {} evals (bf={:.1})",
                    label,
                    promo.old_tier,
                    promo.new_tier,
                    promo.evaluations_at_promotion,
                    promo.branching_factor,
                );
            }
        }

        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "JIT dispatch: hits={}, fallbacks={}, not_compiled={}, errors={}, total={}",
            dispatch.jit_hit,
            dispatch.jit_fallback,
            dispatch.jit_not_compiled,
            dispatch.jit_error,
            dispatch.total,
        );

        // Count actions promoted to each tier level.
        let tier1_count = (0..action_count)
            .filter(|&i| manager.current_tier(i) == tla_jit::CompilationTier::Tier1)
            .count();
        let tier2_count = (0..action_count)
            .filter(|&i| manager.current_tier(i) == tla_jit::CompilationTier::Tier2)
            .count();
        let hit_rate = if dispatch.total > 0 {
            dispatch.jit_hit as f64 / dispatch.total as f64 * 100.0
        } else {
            0.0
        };
        let _ = writeln!(
            out,
            "Summary: {} actions promoted to Tier 1, {} to Tier 2 ({}/{} at Tier 1+, {:.1}% JIT hit rate)",
            tier1_count,
            tier2_count,
            summary.tier1 + summary.tier2,
            summary.total,
            hit_rate,
        );
        let _ = writeln!(out);
        out
    }
}

/// Truncate a label to fit in the column width, appending ".." if shortened.
fn truncate_label(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        format!("{}..", &s[..max - 2])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a `SharedTierState` with custom thresholds for fast promotion in tests.
    fn make_test_state(
        action_count: usize,
        labels: Vec<Option<String>>,
        tier1_threshold: u64,
    ) -> SharedTierState {
        let config = tla_jit::TierConfig::new(tier1_threshold, tier1_threshold * 100);
        let mut manager = tla_jit::TierManager::with_config(action_count, config);
        for i in 0..action_count {
            manager.set_eligible(i);
        }
        let action_eval_counts = (0..action_count)
            .map(|_| AtomicU64::new(0))
            .collect();
        let action_succ_totals = (0..action_count)
            .map(|_| AtomicU64::new(0))
            .collect();
        SharedTierState {
            action_eval_counts,
            action_succ_totals,
            manager: Mutex::new(manager),
            action_labels: labels,
            jit_next_state_cache: OnceLock::new(),
            next_state_jit_hits: AtomicU64::new(0),
            next_state_jit_fallbacks: AtomicU64::new(0),
            next_state_jit_not_compiled: AtomicU64::new(0),
            next_state_jit_errors: AtomicU64::new(0),
            next_state_jit_total: AtomicU64::new(0),
            promotion_history: Mutex::new(Vec::new()),
        }
    }

    #[test]
    fn test_format_tier_report_no_promotions() {
        let state = make_test_state(
            2,
            vec![Some("Enqueue".into()), Some("Dequeue".into())],
            100,
        );
        // Record some evals but not enough to promote.
        for _ in 0..50 {
            state.record_action_eval(0, 3);
            state.record_action_eval(1, 1);
        }
        state.check_promotions();

        let report = state.format_tier_report();
        assert!(
            report.contains("=== Tier Compilation Report ==="),
            "report should have header"
        );
        assert!(report.contains("Enqueue"), "report should list action names");
        assert!(report.contains("Dequeue"), "report should list action names");
        assert!(
            report.contains("Tier0/Interpreter"),
            "actions should be at Tier 0: {report}"
        );
        assert!(
            report.contains("Summary: 0 actions promoted to Tier 1, 0 to Tier 2"),
            "summary should show 0 promotions: {report}"
        );
    }

    #[test]
    fn test_format_tier_report_with_tier1_promotion() {
        let state = make_test_state(
            3,
            vec![
                Some("Send".into()),
                Some("Receive".into()),
                Some("Ack".into()),
            ],
            10, // Low threshold for test
        );
        // Push action 0 and 1 past the tier1 threshold.
        for _ in 0..15 {
            state.record_action_eval(0, 2);
            state.record_action_eval(1, 4);
        }
        // Action 2 stays below threshold.
        for _ in 0..5 {
            state.record_action_eval(2, 1);
        }
        state.check_promotions();

        let report = state.format_tier_report();
        // Send and Receive should be at Tier1.
        assert!(
            report.contains("Tier1/BasicJIT"),
            "promoted actions should show Tier1: {report}"
        );
        // Ack should still be at Tier0.
        assert!(
            report.contains("Tier0/Interpreter"),
            "un-promoted actions should show Tier0: {report}"
        );
        // Summary should show 2 promoted to Tier 1.
        assert!(
            report.contains("Summary: 2 actions promoted to Tier 1, 0 to Tier 2"),
            "summary should show 2 Tier1 promotions: {report}"
        );
        // Promotion events log should be present.
        assert!(
            report.contains("Promotion events:"),
            "promotion events section should exist: {report}"
        );
        assert!(
            report.contains("'Send': Tier0/Interpreter -> Tier1/BasicJIT"),
            "promotion event for Send: {report}"
        );
        assert!(
            report.contains("'Receive': Tier0/Interpreter -> Tier1/BasicJIT"),
            "promotion event for Receive: {report}"
        );
        // Promotions column for promoted actions should show 1.
        // Each promoted action line should have "1" in the Promotions column.
        let send_line = report.lines().find(|l| l.starts_with("Send")).expect("Send line");
        assert!(
            send_line.ends_with('1'),
            "Send promotions count should be 1: {send_line}"
        );
    }

    #[test]
    fn test_format_tier_report_monolithic_next() {
        // When action labels are `None`, the report should show "Next".
        let state = make_test_state(1, vec![None], 5);
        for _ in 0..10 {
            state.record_action_eval(0, 2);
        }
        state.check_promotions();

        let report = state.format_tier_report();
        assert!(report.contains("Next"), "unnamed action should show 'Next': {report}");
        assert!(
            report.contains("Tier1/BasicJIT"),
            "action should be promoted: {report}"
        );
    }

    #[test]
    fn test_format_tier_report_jit_dispatch_counters() {
        let state = make_test_state(1, vec![Some("Act".into())], 100);
        state.record_next_state_dispatch(&tla_jit::NextStateDispatchCounters {
            jit_hit: 80,
            jit_fallback: 10,
            jit_not_compiled: 5,
            jit_error: 5,
            total: 100,
        });

        let report = state.format_tier_report();
        assert!(
            report.contains("JIT dispatch: hits=80, fallbacks=10, not_compiled=5, errors=5, total=100"),
            "JIT dispatch line should have correct counters: {report}"
        );
        assert!(
            report.contains("80.0% JIT hit rate"),
            "hit rate should be 80.0%: {report}"
        );
    }

    #[test]
    fn test_truncate_label_short() {
        assert_eq!(truncate_label("abc", 10), "abc");
    }

    #[test]
    fn test_truncate_label_exact() {
        assert_eq!(truncate_label("abcdefghij", 10), "abcdefghij");
    }

    #[test]
    fn test_truncate_label_long() {
        assert_eq!(truncate_label("abcdefghijk", 10), "abcdefgh..");
    }
}
