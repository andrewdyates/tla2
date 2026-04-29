// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-action evaluation counters for parallel BFS diagnostics.
//!
//! Wave 11a (Part of #4267): this module formerly hosted a tiered JIT
//! promotion manager tied to the Cranelift-backed TierManager. The
//! Cranelift-based JIT is being removed (Epic #4251); this file retains
//! only the plain atomic counting struct that workers use to record
//! action evaluations for end-of-run diagnostics.
//!
//! `SharedTierState` keeps its public API so downstream parallel-BFS
//! callers compile unchanged, but all tier/JIT bookkeeping is gone.
//! Promotion checks are no-ops, `is_promoted_to_jit()` always returns
//! `false`, and `jit_next_state_cache()` always returns `None`.
//!
//! After Wave 7b finishes the broader deletion, this file can be reduced
//! further or folded into a simple `ActionMetrics` struct inline with the
//! worker state.

use std::fmt::{self, Write as _};
use std::sync::atomic::{AtomicU64, Ordering};

/// Next-state JIT dispatch outcome counters.
///
/// Preserved as a plain data struct so parallel-BFS transport files can
/// compile through Wave 11a without pulling in the Cranelift JIT crate.
/// All fields remain zero under the current (post-Cranelift-deletion)
/// code paths.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct NextStateDispatchCounters {
    pub jit_hit: usize,
    pub jit_fallback: usize,
    pub jit_not_compiled: usize,
    pub jit_error: usize,
    pub total: usize,
}

/// Summary of tier distribution across all actions.
///
/// Mirrors the legacy TierSummary shape from `tla-jit` so existing callers
/// (`finalize/resolve.rs`, diagnostic prints) compile unchanged. All
/// tier counts are zero in this reduced module.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TierSummary {
    pub total: usize,
    pub eligible: usize,
    pub interpreter: usize,
    pub tier1: usize,
    pub tier2: usize,
}

impl fmt::Display for TierSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "actions={} eligible={} tier0={} tier1={} tier2={}",
            self.total, self.eligible, self.interpreter, self.tier1, self.tier2
        )
    }
}

/// Thread-safe per-action evaluation counters for parallel BFS.
///
/// Workers call [`SharedTierState::record_action_eval`] on the hot path
/// to increment per-action evaluation/successor counts. No tier
/// promotion logic runs anymore; the main thread's periodic
/// [`SharedTierState::check_promotions`] call is a no-op kept solely to
/// preserve the API surface during Wave 11a.
pub(crate) struct SharedTierState {
    /// Per-action evaluation counts (indexed by action_id).
    action_eval_counts: Vec<AtomicU64>,
    /// Per-action total successor counts for branching-factor stats.
    action_succ_totals: Vec<AtomicU64>,
    /// Cached action labels for diagnostic reports (`None` = monolithic
    /// "Next").
    action_labels: Vec<Option<String>>,
}

impl SharedTierState {
    /// Create a new shared tier state for the given action count.
    ///
    /// `action_labels` provides human-readable names for diagnostic
    /// reports. Pass `None` entries for unnamed/monolithic actions.
    pub(crate) fn new(action_count: usize, action_labels: Vec<Option<String>>) -> Self {
        let action_eval_counts = (0..action_count).map(|_| AtomicU64::new(0)).collect();
        let action_succ_totals = (0..action_count).map(|_| AtomicU64::new(0)).collect();
        SharedTierState {
            action_eval_counts,
            action_succ_totals,
            action_labels,
        }
    }

    /// Whether `action_id` has been promoted to at least the basic-JIT
    /// tier. Always `false` after Wave 11a — the JIT tier machinery is
    /// being deleted.
    #[inline]
    pub(crate) fn is_promoted_to_jit(&self, _action_id: usize) -> bool {
        false
    }

    /// JIT next-state cache, always `None` post-Wave-11a.
    #[inline]
    pub(crate) fn jit_next_state_cache(&self) -> Option<&()> {
        None
    }

    /// Record an action evaluation from a worker thread.
    ///
    /// Called on the BFS hot path after successor generation completes
    /// for a state. Uses `Relaxed` ordering because the counters are
    /// diagnostics only.
    #[inline]
    pub(crate) fn record_action_eval(&self, action_id: usize, successor_count: u64) {
        if let Some(counter) = self.action_eval_counts.get(action_id) {
            counter.fetch_add(1, Ordering::Relaxed);
        }
        if let Some(counter) = self.action_succ_totals.get(action_id) {
            counter.fetch_add(successor_count, Ordering::Relaxed);
        }
    }

    /// Record next-state dispatch counters from a worker thread.
    ///
    /// Preserved as a no-op so transport files retain their call shape.
    /// All dispatch paths that invoked this method have been deleted in
    /// Wave 11a; this method survives only to unblock downstream
    /// cleanup.
    #[inline]
    pub(crate) fn record_next_state_dispatch(&self, _counters: &NextStateDispatchCounters) {}

    /// Periodic promotion check — no-op in the reduced module.
    pub(crate) fn check_promotions(&self) {}

    /// Return a tier summary for end-of-run logging. Always zeroed in
    /// the reduced module.
    pub(crate) fn tier_summary(&self) -> TierSummary {
        TierSummary {
            total: self.action_eval_counts.len(),
            ..TierSummary::default()
        }
    }

    /// Accumulated next-state dispatch counters — always zero after
    /// Wave 11a.
    pub(crate) fn next_state_dispatch_summary(&self) -> NextStateDispatchCounters {
        NextStateDispatchCounters::default()
    }

    /// Print a minimal per-action evaluation report when `--show-tiers`
    /// (`TLA2_SHOW_TIERS=1`) is enabled. All actions report as Tier 0
    /// interpreter because the JIT tier machinery has been removed.
    pub(crate) fn print_tier_report(&self) {
        eprint!("{}", self.format_tier_report());
    }

    /// Format the per-action evaluation report as a `String`.
    pub(crate) fn format_tier_report(&self) -> String {
        let action_count = self.action_eval_counts.len();

        let mut out = String::new();
        let _ = writeln!(out);
        let _ = writeln!(out, "=== Action Evaluation Report ===");
        let _ = writeln!(
            out,
            "{:<30} {:>18} {:>12} {:>10}",
            "Action", "Tier", "Evals", "Avg BF"
        );
        let _ = writeln!(out, "{}", "-".repeat(72));

        for i in 0..action_count {
            let label = self
                .action_labels
                .get(i)
                .and_then(|l| l.as_deref())
                .unwrap_or("Next");
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
            let _ = writeln!(
                out,
                "{:<30} {:>18} {:>12} {:>10.1}",
                truncate_label(label, 30),
                "Tier0/Interpreter",
                evals,
                bf,
            );
        }

        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "Summary: 0 actions promoted to Tier 1, 0 to Tier 2 (0/{} at Tier 1+, 0.0% JIT hit rate)",
            action_count,
        );
        let _ = writeln!(out);
        out
    }
}

/// Truncate a label to fit in the column width, appending ".." if
/// shortened.
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

    #[test]
    fn test_format_tier_report_no_evals() {
        let state = SharedTierState::new(2, vec![Some("Enqueue".into()), Some("Dequeue".into())]);

        let report = state.format_tier_report();
        assert!(
            report.contains("=== Action Evaluation Report ==="),
            "report should have header"
        );
        assert!(
            report.contains("Enqueue"),
            "report should list action names"
        );
        assert!(
            report.contains("Dequeue"),
            "report should list action names"
        );
        assert!(
            report.contains("Tier0/Interpreter"),
            "all actions are Tier 0 post-Wave-11a: {report}"
        );
        assert!(
            report.contains("Summary: 0 actions promoted to Tier 1, 0 to Tier 2"),
            "summary should show 0 promotions: {report}"
        );
    }

    #[test]
    fn test_record_action_eval_accumulates() {
        let state = SharedTierState::new(2, vec![None, None]);
        for _ in 0..5 {
            state.record_action_eval(0, 3);
            state.record_action_eval(1, 1);
        }
        let report = state.format_tier_report();
        // 5 evaluations of action 0 with 3 successors each → avg BF 3.0.
        assert!(
            report.contains("3.0"),
            "action 0 avg BF should be 3.0: {report}"
        );
        // 5 evaluations of action 1 with 1 successor each → avg BF 1.0.
        assert!(
            report.contains("1.0"),
            "action 1 avg BF should be 1.0: {report}"
        );
    }

    #[test]
    fn test_is_promoted_to_jit_always_false() {
        let state = SharedTierState::new(4, vec![None; 4]);
        for i in 0..4 {
            assert!(
                !state.is_promoted_to_jit(i),
                "JIT promotion is disabled post-Wave-11a"
            );
        }
    }

    #[test]
    fn test_jit_next_state_cache_always_none() {
        let state = SharedTierState::new(1, vec![None]);
        assert!(
            state.jit_next_state_cache().is_none(),
            "JIT next-state cache is unavailable post-Wave-11a"
        );
    }

    #[test]
    fn test_check_promotions_is_noop() {
        let state = SharedTierState::new(1, vec![Some("Next".into())]);
        for _ in 0..100 {
            state.record_action_eval(0, 2);
        }
        state.check_promotions();
        let report = state.format_tier_report();
        assert!(
            report.contains("Tier0/Interpreter"),
            "no promotions should fire: {report}"
        );
    }

    #[test]
    fn test_tier_summary_zeroed() {
        let state = SharedTierState::new(3, vec![None; 3]);
        let summary = state.tier_summary();
        assert_eq!(summary.total, 3);
        assert_eq!(summary.eligible, 0);
        assert_eq!(summary.tier1, 0);
        assert_eq!(summary.tier2, 0);
    }

    #[test]
    fn test_next_state_dispatch_summary_zeroed() {
        let state = SharedTierState::new(1, vec![None]);
        state.record_next_state_dispatch(&NextStateDispatchCounters {
            jit_hit: 80,
            total: 100,
            ..Default::default()
        });
        // record_next_state_dispatch is a no-op.
        let summary = state.next_state_dispatch_summary();
        assert_eq!(summary.jit_hit, 0);
        assert_eq!(summary.total, 0);
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
