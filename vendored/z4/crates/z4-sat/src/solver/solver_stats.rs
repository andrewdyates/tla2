// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure telemetry counters sub-struct for hot/cold field separation (#5090).
//!
//! Groups write-only telemetry counters into a single struct so the
//! Solver's hot BCP fields are not intermixed with cold diagnostic state.
//! All fields are incremented in hot paths but never read for scheduling
//! decisions — only for stats display and diagnostic traces.

use crate::diagnostic_trace::DiagnosticPass;

pub(crate) const INPROCESS_TIMING_LABELS: [&str; 15] = [
    "inproc_decompose_ms",
    "inproc_htr_ms",
    "inproc_subsume_ms",
    "inproc_probe_ms",
    "inproc_backbone_ms",
    "inproc_congruence_ms",
    "inproc_bve_ms",
    "inproc_factor_ms",
    "inproc_bce_ms",
    "inproc_cce_ms",
    "inproc_condition_ms",
    "inproc_transred_ms",
    "inproc_sweep_ms",
    "inproc_vivify_ms",
    "inproc_reorder_ms",
];

pub(crate) fn inprocessing_timing_index(pass: DiagnosticPass) -> Option<usize> {
    match pass {
        DiagnosticPass::Decompose => Some(0),
        DiagnosticPass::HTR => Some(1),
        DiagnosticPass::Subsume => Some(2),
        DiagnosticPass::Probe => Some(3),
        DiagnosticPass::Backbone => Some(4),
        DiagnosticPass::Congruence => Some(5),
        DiagnosticPass::BVE => Some(6),
        DiagnosticPass::Factor => Some(7),
        DiagnosticPass::BCE => Some(8),
        DiagnosticPass::CCE => Some(9),
        DiagnosticPass::Condition => Some(10),
        DiagnosticPass::TransRed => Some(11),
        DiagnosticPass::Sweep => Some(12),
        DiagnosticPass::Vivify => Some(13),
        DiagnosticPass::Reorder => Some(14),
        _ => None,
    }
}

/// Pure telemetry counters (incremented in hot paths, read only for stats display).
///
/// These counters are never consulted for scheduling decisions (restart,
/// reduce_db, inprocessing). They exist purely for performance diagnostics
/// and user-facing statistics. Grouping them reduces the Solver's direct
/// field count and clarifies the hot/cold boundary.
///
/// Reference: CaDiCaL `Stats` struct groups all counters separately from
/// solver state.
pub(crate) struct SolverStats {
    /// Chronological backtrack count.
    pub chrono_backtracks: u64,
    /// Number of same-level blocks considered for block-UIP shrinking.
    pub shrink_block_attempts: u64,
    /// Number of block-UIP searches that found a replacement literal.
    pub shrink_block_successes: u64,
    /// BCP telemetry: blocker-fastpath hits (`blocker_val > 0`).
    pub bcp_blocker_fastpath_hits: u64,
    /// BCP telemetry: binary watcher path hits.
    pub bcp_binary_path_hits: u64,
    /// BCP telemetry: literals examined in replacement scans.
    pub bcp_replacement_scan_steps: u64,
    /// Level-0 preprocess telemetry: literals removed as root-false.
    pub preprocess_level0_literals_removed: u64,
    /// Level-0 preprocess telemetry: satisfied clauses deleted.
    pub preprocess_level0_satisfied_deleted: u64,
    /// Total random decisions made.
    pub random_decisions: u64,
    /// OTFS (on-the-fly self-subsumption) strengthening count.
    pub otfs_strengthened: u64,
    /// OTFS (on-the-fly self-subsumption) trigger count.
    pub otfs_subsumed: u64,
    /// OTFS diagnostic: candidate count (resolvent_size < antecedent_size).
    pub otfs_candidates: u64,
    /// OTFS diagnostic: blocked by open==0.
    pub otfs_blocked_open0: u64,
    /// OTFS diagnostic: blocked by watch invariant.
    pub otfs_blocked_watch: u64,
    /// OTFS diagnostic: blocked by otfs_strengthen returning false.
    pub otfs_blocked_strengthen: u64,
    /// Forced-literal early return count (CaDiCaL analyze.cpp:977-1004).
    /// Single literal at conflict level → skip 1UIP, use clause as driver.
    pub forced_backtracks: u64,
    /// Focused-mode Glucose EMA checks (number of times condition was evaluated).
    pub focused_ema_checks: u64,
    /// Focused-mode Glucose EMA fires (condition was true → restart).
    pub focused_ema_fires: u64,
    /// Stable-mode reluctant doubling fires (countdown reached 0 → restart).
    pub stable_reluctant_fires: u64,
    /// Cumulative sum of LBD values fed to EMA updates.
    pub lbd_sum: u64,
    /// Count of LBD values fed to EMA updates.
    pub lbd_count: u64,
    /// Focused-mode: EMA condition true but blocked by conflict gate.
    pub focused_ema_blocked_by_conflict_gate: u64,
    /// Focused-mode decisions (for computing focused dec/confl).
    pub focused_decisions: u64,
    /// Stable-mode decisions.
    pub stable_decisions: u64,
    /// Cumulative per-pass inprocessing wall time in nanoseconds.
    pub inprocessing_time_ns: [u64; INPROCESS_TIMING_LABELS.len()],
    /// Number of completed inprocessing rounds (#8099).
    pub inprocessing_rounds: u64,
    /// Total simplifications across all inprocessing rounds (#8099).
    /// Counts clauses removed + literals strengthened per round.
    pub inprocessing_simplifications: u64,
    /// Wall-clock time spent in preprocessing phase (nanoseconds).
    pub preprocess_time_ns: u64,
    /// Wall-clock time spent in CDCL search loop (nanoseconds).
    pub search_time_ns: u64,
    /// Wall-clock time spent in lucky-phase probing (nanoseconds).
    pub lucky_time_ns: u64,
    /// Wall-clock time spent in walk-based phase initialization (nanoseconds).
    pub walk_time_ns: u64,
    /// Number of MAB arm switches (branch heuristic changes via UCB1).
    pub mab_arm_switches: u64,
    /// JIT: propagations discovered by JIT-compiled BCP.
    pub jit_propagations: u64,
    /// JIT: conflicts found by JIT-compiled BCP.
    pub jit_conflicts: u64,
    /// JIT: compile time in microseconds.
    pub jit_compile_time_us: u64,
    /// JIT: number of clauses compiled into native code.
    pub jit_clauses_compiled: u64,
    /// JIT: total 2WL watch entries detached for JIT-compiled clauses (#8005).
    pub jit_watches_detached: u64,
    /// JIT: total 2WL watch entries reattached after JIT invalidation (#8005).
    pub jit_watches_reattached: u64,
    /// JIT: number of inprocessing rounds where recompilation was skipped
    /// because only deletion-only passes ran (guard bits handle deletion).
    pub jit_recompilations_skipped: u64,
    /// JIT: number of full recompilations after structural inprocessing passes.
    pub jit_recompilations: u64,
}

impl SolverStats {
    /// Create zeroed telemetry counters.
    pub(crate) fn new() -> Self {
        Self {
            chrono_backtracks: 0,
            shrink_block_attempts: 0,
            shrink_block_successes: 0,
            bcp_blocker_fastpath_hits: 0,
            bcp_binary_path_hits: 0,
            bcp_replacement_scan_steps: 0,
            preprocess_level0_literals_removed: 0,
            preprocess_level0_satisfied_deleted: 0,
            random_decisions: 0,
            otfs_strengthened: 0,
            otfs_subsumed: 0,
            otfs_candidates: 0,
            otfs_blocked_open0: 0,
            otfs_blocked_watch: 0,
            otfs_blocked_strengthen: 0,
            forced_backtracks: 0,
            focused_ema_checks: 0,
            focused_ema_fires: 0,
            stable_reluctant_fires: 0,
            lbd_sum: 0,
            lbd_count: 0,
            focused_ema_blocked_by_conflict_gate: 0,
            focused_decisions: 0,
            stable_decisions: 0,
            inprocessing_time_ns: [0; INPROCESS_TIMING_LABELS.len()],
            inprocessing_rounds: 0,
            inprocessing_simplifications: 0,
            preprocess_time_ns: 0,
            search_time_ns: 0,
            lucky_time_ns: 0,
            walk_time_ns: 0,
            mab_arm_switches: 0,
            jit_propagations: 0,
            jit_conflicts: 0,
            jit_compile_time_us: 0,
            jit_clauses_compiled: 0,
            jit_watches_detached: 0,
            jit_watches_reattached: 0,
            jit_recompilations_skipped: 0,
            jit_recompilations: 0,
        }
    }

    pub(crate) fn record_inprocessing_time(&mut self, pass: DiagnosticPass, elapsed_ns: u64) {
        if let Some(index) = inprocessing_timing_index(pass) {
            self.inprocessing_time_ns[index] =
                self.inprocessing_time_ns[index].saturating_add(elapsed_ns);
        }
    }
}
